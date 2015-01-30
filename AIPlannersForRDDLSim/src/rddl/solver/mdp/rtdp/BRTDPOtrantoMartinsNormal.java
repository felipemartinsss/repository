package rddl.solver.mdp.rtdp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import dd.discrete.ADD;
import dd.discrete.DD;

import rddl.ActionGenerator;
import rddl.EvalException;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.State;
import rddl.policy.Policy;
import rddl.policy.SPerseusSPUDDPolicy;
import rddl.solver.DDUtils;
import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Pair;



/**
 * This class implements a RTDP policy that is not factored.
 * 
 * An example of how to run this policy in the solver is as follow:
 * ./run rddl.sim.Simulator files/final_comp/rddl rddl.solver.mdp.rtdp.RTDPOtranto sysadmin_inst_mdp__1 rddl.viz.SysAdminScreenDisplay
 * 
 * @author Felipe Martins
 * @author Guilherme Otranto
 **/

@SuppressWarnings({ "unchecked", "rawtypes" })
public class BRTDPOtrantoMartinsNormal extends Policy
{
	private static double SOLVER_TIME_LIMIT_PER_TURN = 2;
	private static int MAX_TRIAL_DEPTH = 7;

	//This will be used to decide whether or not to do backwards updates on Q during RTDP trials
	private boolean backwardsUpdateQ = false;
	private ADD context;
	private ArrayList<Integer> ADDs;
	private ArrayList<CString> stateVars;
	private ArrayList<CString> actionNames;
	private HashMap<CString, Action> actionBridge; //Bridge from action name to Action object

	private int remainingHorizon;
	private int horizon;

	private RDDL2Format translation; //The problem represented as 

	// Variables used to run interactions
	private INSTANCE rddl = null;
	private int upperValueOfDD;
	private int lowerValueOfDD;
	private int trials;
	//private double rewardRange; // Important if approximating
	private double discount;
	private CString bestActionAtInit;
	private HashMap<Integer,Integer> prime2NonPrimeIDs;

	//Variable to keep track of time during trials
	private long startTime;

	//Randomizer in case we cannot get an actual planned action
	private Random rand = new Random();

	// Dummy Constructors
	public BRTDPOtrantoMartinsNormal() { }

	public BRTDPOtrantoMartinsNormal(String instance_name) {
		super(instance_name);
	}

	/**
	 * This method creates the problem representation used in the planning using the ADD "framework" provided.
	 * 
	 * It returns after a list of state variables, actionNames and a Map<CString,Action> have been created using
	 * actionNames as keys and the corresponding Action object as values.
	 * 
	 * The Adds data structure is also created (one reward followed by n cpt for each action, n is the number of state variables).
	 **/
	public void roundInit(double time_left, int horizon, int round_number, int total_rounds) 
	{
		this.remainingHorizon = horizon;

		//Build ADDs for transition, reward and value function
		if (translation == null) 
		{
			//Build ADD translation of our current problem (indicated by _sInstanceName inherited from Policy)
			try
			{
				translation = new RDDL2Format(this._rddl, this._sInstanceName, RDDL2Format.SPUDD_CURR, "");
			} 
			catch (Exception e) 
			{
				System.err.println("Could not construct MDP for: " + this._sInstanceName + "\n" + e);
				e.printStackTrace(System.err);
				System.exit(1);
			}

			//Get ADD context
			context = translation._context;
			//Initialize value function ADD
			ADDs = new ArrayList<Integer>();

			//Get the state variables and action names
			stateVars = new ArrayList<CString>();
			for (String s : translation._alStateVars) {
				stateVars.add(new CString(s));
			}
			actionNames = new ArrayList<CString>();
			for (String a : translation._hmActionMap.keySet())
			{
				actionNames.add(new CString(a));
			}

			//Extract the reward and transition ADDs
			actionBridge = new HashMap<CString,Action>();
			for (String a : translation._hmActionMap.keySet()) 
			{
				HashMap<CString,Integer> cpts = new HashMap<CString,Integer>();
				int reward = context.getConstantNode(0d);

				//Build reward from additive decomposition
				ArrayList<Integer> reward_summands = translation._act2rewardDD.get(a);
				for (int summand : reward_summands)
				{
					reward = context.applyInt(reward, summand, ADD.ARITH_SUM);
				}
				ADDs.add(reward);

				//Build CPTs for the action at hand
				for (String s : translation._alStateVars) 
				{
					int dd = translation._var2transDD.get(new Pair(a, s));

					int dd_true  = context.getVarNode(s + "'", 0d, 1d);
					dd_true = context.applyInt(dd_true, dd, ADD.ARITH_PROD);

					int dd_false = context.getVarNode(s + "'", 1d, 0d);
					int one_minus_dd = context.applyInt(context.getConstantNode(1d), dd, ADD.ARITH_MINUS);
					dd_false = context.applyInt(dd_false, one_minus_dd, ADD.ARITH_PROD);

					int cpt = context.applyInt(dd_true, dd_false, ADD.ARITH_SUM);

					cpts.put(new CString(s + "'"), cpt);
					ADDs.add(cpt);
				}

				//Build Action and add to HashMap
				CString action_name = new CString(a);
				Action action = new Action(context, action_name, cpts, reward);
				actionBridge.put(action_name, action);
			}

			//Initialize RTDP solver
			initSolver();
		}
	}

	/**
	 * This method initializes the necessary variables to run the interactions needed on RTDP planning.
	 * 
	 * It returns after the discount, the horizon and rewardRange have been initialized.
	 **/
	public void initSolver() {
		trials = -1;
		rddl = _rddl._tmInstanceNodes.get(this._sInstanceName);
		if (rddl == null) 
		{
			System.err.println("ERROR: Could not fine RDDL instance '" + rddl + "'");
			System.exit(1);
		}

		discount = rddl._dDiscount;
		if (discount == 1)
			discount = 0.99;

		horizon = rddl._nHorizon;

		//Creates the bridge between primed CPT head variables and their non-prime state variable equivalents
		prime2NonPrimeIDs = new HashMap<Integer,Integer>();
		for (Map.Entry<String, String> me : translation._hmPrimeRemap.entrySet()) {
			String var = me.getKey();
			String var_prime = me.getValue();
			Integer var_id = (Integer)context._hmVarName2ID.get(var);
			Integer var_prime_id = (Integer)context._hmVarName2ID.get(var_prime);
			if (var_id == null || var_prime_id == null) {
				System.err.println("ERROR: Could not get var IDs " 
						+ var_id + "/" + var_prime_id
						+ " for " + var + "/" + var_prime);
				System.exit(1);
			}
			prime2NonPrimeIDs.put(var_prime_id, var_id);
		}

		double rewardUp = 0;
		double rewardDown = Double.MAX_VALUE;
		for (Action a : actionBridge.values())
		{
			rewardUp = Math.max(rewardUp, context.getMaxValue(a._reward));
			rewardDown = Math.min(rewardDown, context.getMinValue(a._reward));
		}
		
		// Initializes upper and lower bounds
		double upperBound;
		double lowerBound;
		if (discount < 1)
		{
			upperBound = rewardUp/(1 - discount);
			lowerBound = rewardDown/(1 - discount);
		}
		else
		{
			upperBound = horizon * rewardUp;
			lowerBound = horizon * rewardDown; 
		}
		upperValueOfDD = context.getConstantNode(upperBound);
		lowerValueOfDD = context.getConstantNode(lowerBound);

		// context.getGraph(upperValueOfDD).launchViewer();
		// context.getGraph(lowerValueOfDD).launchViewer();
	}

	/**
	 * This method returns the best action for the given state. It can return a random one if 
	 * a best action cannot be calculated in time.
	 **/
	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException 
	{
		//Just checking if system messed up and sent a null state in MDP problem...
		if (s == null) 
		{
			System.err.println("ERROR: A null State is not an acceptable parameter.");
			System.exit(1);
		}

		//Since the system doesn't support working directly with the states, we extract the fluents
		//and use the ArrayList representation of the State s.
		ArrayList currentState = DDUtils.ConvertTrueVars2DDAssign(context, 
				CString.Convert2CString(SPerseusSPUDDPolicy.getTrueFluents(s, "states")), 
				stateVars);

		//RTDP algorithm proper:
		bestActionAtInit = null;
		doBRTDP(currentState);

		String actionTaken = null;
		if(bestActionAtInit != null)
		{
			actionTaken = bestActionAtInit._string;
		}

		//Get a bridge between action names and their ArrayList<PVAR_INST_DEF> representation, to return a proper action.
		Map<String, ArrayList<PVAR_INST_DEF>> actionMap = ActionGenerator.getLegalBoolActionMap(s);

		//If no good action is found, do a random one: transform the Set into list and randomize a index...
		if (actionTaken == null || trials < 1) 
		{
			ArrayList<String> actions = new ArrayList<String>(actionMap.keySet());
			actionTaken = actions.get(rand.nextInt(actions.size()));
		} 

		remainingHorizon--;
		return actionMap.get(actionTaken);
	}

	/**
	 * This method constantly calls for a new RTDP trial to be made.
	 * This ensures that the planning is constantly better but can be
	 * stopped at any moment..
	 **/
	private void doBRTDP(ArrayList initState)
	{
		//Mark the time we started
		startTime = System.currentTimeMillis();		
		
		try 
		{
			trials = 0;
			while(true) 
			{
				executeTrial(initState, Math.min(remainingHorizon, MAX_TRIAL_DEPTH));
				trials++;
			}
		}
		catch (TimeOutException e) 
		{
			System.out.println("Managed " + trials + " trials, action choosen: " + bestActionAtInit);
		}
		catch (Exception e) 
		{
			System.err.println("RTDP: ERROR at trial" + trials);
			e.printStackTrace(System.err);
			System.exit(1);
		}
	}

	/**
	 * This method executes a single RTDP trial and updates the best action found so far.
	 **/
	private void executeTrial(ArrayList initState, int trialDepth) throws TimeOutException 
	{
		//Start trial with no selected actions, from initial state.
		CString bestAction = null;		
		ArrayList currState = initState;

		ArrayList<ArrayList> visited = new ArrayList<ArrayList>(trialDepth);

		//Go to the horizon, choosing next states through coin toss and calculating the Q function
		for (int i = trialDepth; i > 0; i--)
		{
			//Flush caches and check time limit
			flushCaches();
			checkTimeLimit();

			if (backwardsUpdateQ)
				visited.add(currState);

			// Find the best action for currState and compute Q (lower)
			QValue lowerResult = selectQValue(currState, lowerValueOfDD);

			// Find the best action for currState and compute Q (upper)
			QValue upperResult = selectQValue(currState, upperValueOfDD);

			if (bestAction == null)
			{
				bestActionAtInit = upperResult.action;
				bestAction = upperResult.action;
			}

			// Update Q
			upperValueOfDD = DDUtils.UpdateValue(context, upperValueOfDD, currState, upperResult.qValue);
			lowerValueOfDD = DDUtils.UpdateValue(context, lowerValueOfDD, currState, lowerResult.qValue);

			if (i > 1)
				currState = chooseNextState(currState, upperResult.action, lowerValueOfDD, upperValueOfDD);
		}

		//Update Q in reverse order if backwardsUpdateQ is set to true
		if (backwardsUpdateQ)
		{
			for (int depth = visited.size() - 1; depth >= 0; depth--) 
			{
				// Flush caches and check time limit
				flushCaches();
				checkTimeLimit();

				currState = visited.get(depth);

				// Find the best action for currState and compute Q (lower)
				QValue lowerResult = selectQValue(currState, lowerValueOfDD);
				lowerValueOfDD = DDUtils.UpdateValue(context, lowerValueOfDD, currState, lowerResult.qValue);

				// Find the best action for currState and compute Q (upper)
				QValue upperResult = selectQValue(currState, upperValueOfDD);
				upperValueOfDD = DDUtils.UpdateValue(context, upperValueOfDD, currState, upperResult.qValue);


				// If back to initial state then update best action
				if (depth == 0) 
					bestActionAtInit = upperResult.action;
			}
		}
	}

	/**
	 * This method creates the next state by randomizing (using the correct probabilities) what values
	 * the variables affected by the action will have. (The RTDP coin toss happens here, only using the factored representation).
	 * @param lowerValueFunction TODO
	 * @param upperValueFunction TODO
	 * @param tau TODO
	 * @param initialState TODO
	 **/
	private ArrayList chooseNextState(ArrayList currentState, CString action, int lowerValueFunction, int upperValueFunction) 
	{
		// Calcula VGap entre ADDs
		int gapValueFunction = context.applyInt(upperValueFunction, lowerValueFunction, ADD.ARITH_MINUS);
		// Visualiza ADD de VGap
		// context.getGraph(gapValueFunction).launchViewer();

		Action a = actionBridge.get(action);
		//First off, copy the current state, next state is the same, except where the action modifies it...
		ArrayList nextState = (ArrayList)currentState.clone();

		double totalB = 0;
		Map<Map.Entry<Integer, Integer>, Double> BValues = new HashMap<Map.Entry<Integer, Integer>, Double>();
		
		//For each variable the action can change, put the CPT in VGap
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet()) 
		{
			List<Map.Entry<Integer, Integer>> fluents = new ArrayList<Map.Entry<Integer, Integer>>();
			fluents.addAll(a._hmVarID2CPT.entrySet());
			
			double b = calculateBfunction(currentState, gapValueFunction, fluents, fluents.size());
			BValues.put(var, b);
			totalB += b;
		}
				
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet()) 
		{
			//Randomize the variable value based on the calculated b(var)/B
			boolean newValue = rand.nextDouble() < BValues.get(var)/totalB;

			// Assign truth value to level for unprimed variable
			int varID = prime2NonPrimeIDs.get(var.getKey());
			int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
			nextState.set(levelUnprime, newValue);
		}
		return nextState;
	}
	
	/**
	 * This method creates the next state by randomizing our 'secret' method, explained in the report.
	 **/
	private ArrayList chooseNextStateAlt(ArrayList currentState, CString action, int lowerValueFunction, int upperValueFunction) 
	{
		// Calcula VGap entre ADDs
		int gapValueFunction = context.applyInt(upperValueFunction, lowerValueFunction, ADD.ARITH_MINUS);

		Action a = actionBridge.get(action);
		//First off, copy the current state, next state is the same, except where the action modifies it...
		ArrayList nextState = (ArrayList)currentState.clone();

		Map.Entry<Integer, Integer> mostDividedVar = null, secMostDividedVar =null, thirdMostDividedVar = null;
		
		double distance = 100;
		//Find the most divided variable
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet())
		{
			if (Math.abs(calculateProbInNewState(currentState, var) - .5d) < distance)
			{
				mostDividedVar = var;
				distance = Math.abs(calculateProbInNewState(currentState, var) - .5d);
			}
		}
		//Find the second most divided variable
		distance = 100;
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet())
		{
			if (Math.abs(calculateProbInNewState(currentState, var) - .5d) < distance)
			{
				if (!var.equals(mostDividedVar))
				{
					secMostDividedVar = var;
					distance = Math.abs(calculateProbInNewState(currentState, var) - .5d);
				}
			}
		}
		//Find the third most divided variable
		distance = 100;
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet())
		{
			if (Math.abs(calculateProbInNewState(currentState, var) - .5d) < distance)
			{
				if (!var.equals(mostDividedVar) && !var.equals(secMostDividedVar))
				{
					thirdMostDividedVar = var;
					distance = Math.abs(calculateProbInNewState(currentState, var) - .5d);
				}
			}
		}
		
		//Construct the most probable state
		Map <ArrayList, Double>states2Probabilities = new HashMap<ArrayList, Double>();
		double prob = 1;
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet()) 
		{
			//Randomize the variable value based on the calculated b(var)/B
			boolean newValue;
			if (calculateProbInNewState(currentState, var) < .5d)
			{
				newValue = false;
				prob *= (1 - calculateProbInNewState(currentState, var));
			}
			else
			{
				newValue = true;
				prob *= calculateProbInNewState(currentState, var);
			}
			
			// Assign truth value to level for unprimed variable
			int varID = prime2NonPrimeIDs.get(var.getKey());
			int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
			nextState.set(levelUnprime, newValue);
		}
		states2Probabilities.put(nextState, prob);
		
		//Create other 'probable' future states using the most divided variables
		ArrayList p1 = switchVariableInState(nextState, prob, states2Probabilities, mostDividedVar, currentState);
		ArrayList p2 = switchVariableInState(nextState, prob, states2Probabilities, secMostDividedVar, currentState);
		switchVariableInState(nextState, prob, states2Probabilities, thirdMostDividedVar, currentState);
		
		ArrayList p1p2 = switchVariableInState(p1, states2Probabilities.get(p1), states2Probabilities, secMostDividedVar, currentState);
		switchVariableInState(p1, states2Probabilities.get(p1), states2Probabilities, thirdMostDividedVar, currentState);
		
		switchVariableInState(p2, states2Probabilities.get(p2), states2Probabilities, thirdMostDividedVar, currentState);
		
		switchVariableInState(p1p2, states2Probabilities.get(p1p2), states2Probabilities, thirdMostDividedVar, currentState);
		
		double total = 0;
		for (ArrayList state : states2Probabilities.keySet())
		{
			double value = states2Probabilities.get(state)*context.evaluate(gapValueFunction, state);
			total += value;
			states2Probabilities.put(state, value);
		}
		
		for (ArrayList state : states2Probabilities.keySet())
		{
			if (rand.nextDouble() < states2Probabilities.get(state)/total)
				return state;
		}		
		return nextState;
	}
	
	private ArrayList switchVariableInState(ArrayList state, double prob, Map<ArrayList, Double> map, Map.Entry<Integer, Integer> var, ArrayList currentState)
	{
		ArrayList newState = (ArrayList)state.clone();
		double newProb = prob;
		int varID = prime2NonPrimeIDs.get(var.getKey());
		int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
		if (calculateProbInNewState(currentState, var) < .5d)
		{
			newState.set(levelUnprime, true);
			newProb /= (1-calculateProbInNewState(currentState, var));
			newProb *= calculateProbInNewState(currentState, var);
		}
		else
		{
			newState.set(levelUnprime, false);
			newProb /= calculateProbInNewState(currentState, var);
			newProb *= (1-calculateProbInNewState(currentState, var));
		}
		map.put(newState, newProb);
		
		return newState;
	}

	/**
	 * This method uses the framework to calculate and return the probability that a state variable will 
	 * be true in the next state if the action is applied. The framework way to do this is less than ideal...
	 **/
	private double calculateProbInNewState(ArrayList currentState, Map.Entry<Integer, Integer> variable)
	{
		int level = (Integer) context._hmGVarToLevel.get(variable.getKey());
		currentState.set(level, true);
		double prob = context.evaluate(variable.getValue(), currentState);
		if (Double.isNaN(prob)) {
			System.err.println("Probability of variable being true is not a single value.");
			System.exit(1);
		}
		currentState.set(level, null);

		return prob;
	}
	
	/**
	 * This method calculates b(fluent) using recursive calling to find the result of equation 9, of
	 * the paper Symbolic BRTDP.
	 **/
	private double calculateBfunction(ArrayList currentState, int Vgap, List<Map.Entry<Integer, Integer>> fluents, int remaining)
	{
		if (remaining == 1)
		{
			double returnValue = 0;
			
			ArrayList nextState = (ArrayList)currentState.clone();			
			
			int varID = prime2NonPrimeIDs.get(fluents.get(fluents.size()-remaining).getKey());
			int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
			nextState.set(levelUnprime, true);
			double probTrue = calculateProbInNewState(currentState, fluents.get(fluents.size()-remaining));
			returnValue += probTrue*context.evaluate(Vgap, nextState);
			
			nextState.set(levelUnprime, false);
			returnValue += (1-probTrue)*context.evaluate(Vgap, nextState);
			
			return returnValue;
		}
		
		double returnValue = 0;
		
		ArrayList nextState = (ArrayList)currentState.clone();
		
		int varID = prime2NonPrimeIDs.get(fluents.get(fluents.size()-remaining).getKey());
		int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
		nextState.set(levelUnprime, true);
		double probTrue = calculateProbInNewState(currentState, fluents.get(fluents.size()-remaining));
		returnValue += probTrue*calculateBfunction(nextState, Vgap, fluents, remaining-1);
		
		nextState.set(levelUnprime, false);
		returnValue += (1-probTrue)*calculateBfunction(nextState, Vgap, fluents, remaining-1);
		
		return returnValue;
	}

	/**
	 * This method returns the best action and its perceived value for the current state (in a QValue instance).
	 * It does this by calculating Q for every viable action from the state given and selecting the best one.
	 * @param valueFunction TODO
	 **/
	private QValue selectQValue(ArrayList state, int valueOfDD) 
	{
		int valueFunction = context.remapGIDsInt(valueOfDD, translation._hmPrimeRemap);

		QValue result = new QValue(null, -Double.MAX_VALUE); 
		//For every action update the Q value and then get the best one
		for (Map.Entry<CString, Action> action : actionBridge.entrySet())
		{
			Action a = action.getValue();
			double qvalue = calcQValue(valueFunction, state, a._csActionName);
			
			if (result.action == null || qvalue > result.qValue) 
			{ 
				result.action = a._csActionName;
				result.qValue = qvalue;
			}
		}
		return result;
	}

	/**
	 * This method returns the Q value for a given action on a given state.
	 * The trick to dealing with the factored representation is similar to the one used
	 * in the chooseNextState. Every variable changed is accounted and the final value is 
	 * the same as if all states were computed independently.
	 **/
	private double calcQValue(int valueFunction, ArrayList state, CString action) 
	{
		Action a = actionBridge.get(action);

		Set valueFuncionGIDs = context.getGIDs(valueFunction);

		//Each variable the action can change needs to be inserted into the calculation
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet()) 
		{
			int varID = var.getKey();
			
			//If the variable doesn't appear in the value function, skip it
			if (valueFuncionGIDs.contains(varID)) 
			{
				//Calculate the probability of the variable being true after action is applied
				double prob = calculateProbInNewState(state, var);
							
				int futureVarDBN = context.getVarNode(varID, 1-prob, prob);
				
				//ValueFunction incorporates the future variable and its DBN
				valueFunction = context.applyInt(valueFunction, futureVarDBN, DD.ARITH_PROD);
				valueFunction = context.opOut(valueFunction, varID, DD.ARITH_SUM);
			}			
		}

		//Get the rewards (current and expected)
		double expectedReward = context.evaluate(valueFunction, (ArrayList)null); 
		double currReward = context.evaluate(a._reward, state);
		
		//qValue is then current reward plus the discounted expected reward
		return currReward + discount * expectedReward;
	}

	/**
	 * This helper class holds an action name and its calculated qValue for the interaction.
	 **/
	private static class QValue 
	{
		public CString action;
		public double  qValue;
		public QValue(CString action, double qValue)
		{
			this.action = action;
			this.qValue  = qValue;
		}
	}

	private void flushCaches() 
	{
		context.clearSpecialNodes();
		for (Integer dd : ADDs)
			context.addSpecialNode(dd);
				context.addSpecialNode(upperValueOfDD);
				context.addSpecialNode(lowerValueOfDD);

				context.flushCaches(false);
	}

	private void checkTimeLimit() throws TimeOutException 
	{
		double elapsed_time = (System.currentTimeMillis() - startTime) / 1000;
		if (elapsed_time > SOLVER_TIME_LIMIT_PER_TURN)
			throw new TimeOutException("Time limit exceded.");
	}
}