package rddl.solver.mdp.rtdp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import dd.discrete.ADD;
import dd.discrete.DD;

import rddl.ActionGenerator;
import rddl.EvalException;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.REAL_CONST_EXPR;
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
 * This class was implemented based on RTDPOtranto and a minor change in order to better exploit the nature of the system representation
 * of the problems. Occam's razor offers an explanation as to why this does so well here.
 * 
 * An example of how to run this policy in the solver is as follow:
 * ./run rddl.sim.Simulator files/final_comp/rddl rddl.solver.mdp.rtdp.HappyHappyGoLucky sysadmin_inst_mdp__1 rddl.viz.SysAdminScreenDisplay
 * 
 * @author Guilherme Otranto
 **/
@SuppressWarnings({ "unchecked", "rawtypes" })
public class HappyHappyGoLucky extends Policy
{
	private static double SOLVER_TIME_LIMIT_PER_TURN = 0.2d;
	
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
	private int valueOfDD;
	private int trials;
	private double rewardRange; // Important if approximating
	private double discount;
	private CString bestActionAtInit;
	private HashMap<Integer,Integer> prime2NonPrimeIDs;
	
	//Variable to keep track of time during trials
	private long startTime;
	
	//Randomizer in case we cannot get an actual planned action
	private Random rand = new Random();
	private REAL_CONST_EXPR exp;
	
	// Dummy Constructors
	public HappyHappyGoLucky() { }

	public HappyHappyGoLucky(String instance_name) {
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
			exp = new REAL_CONST_EXPR(10d);
			
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
		
		rewardRange = 0;
		for (Action a : actionBridge.values())
			rewardRange = Math.max(rewardRange,	context.getMaxValue(a._reward) - context.getMinValue(a._reward));
		
		//Initializes with a *very* optimistic upper bound
		double upperBound;
		if (discount < 1)
		{
			upperBound = rewardRange/(1 - discount);
		}
		else
		{
			upperBound = horizon * rewardRange;
		}
		valueOfDD = context.getConstantNode(upperBound);			
	}
	
	/**
	 * This method constantly calls for a new RTDP trial to be made.
	 * This ensures that the planning is constantly better but can be
	 * stopped at any moment..
	 **/
	private void doRTDP(ArrayList initState)
	{
		//Mark the time we started
		startTime = System.currentTimeMillis();

		try 
		{
			trials = 0;
			while(true) 
			{
				checkTimeLimit();
				executeTrial(initState);
				trials++;
			}
		}
		catch (TimeOutException e) 
		{
		}
		catch (Exception e) 
		{
			System.err.println("RTDP: ERROR at trial" + trials);
			e.printStackTrace(System.err);
			System.exit(1);
		}
	}
	
	/**
	 * This method creates the next state by randomizing (using the correct probabilities) what values
	 * the variables affected by the action will have. (The RTDP coin toss happens here, only using the factored representation).
	 **/
	private ArrayList chooseNextState(ArrayList currentState, CString action) 
	{
		Action a = actionBridge.get(action);
		
		//First off, copy the current state, next state is the same, except where the action modifies it...
		ArrayList nextState = (ArrayList)currentState.clone();

		//For each variable the action can change, randomize the value based on the probability and set it on the nextState
		for (Map.Entry<Integer, Integer> var : a._hmVarID2CPT.entrySet()) 
		{
			double prob = calculateProbInNewState(currentState, var);
					
			//Randomize the variable value based on the calculated probability
			boolean newValue = rand.nextDouble() < prob;

			// Assign truth value to level for unprimed variable
			int varID = prime2NonPrimeIDs.get(var.getKey());
			int levelUnprime = (Integer)context._hmGVarToLevel.get(varID);
			nextState.set(levelUnprime, newValue);
		}
		return nextState;
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
				stateVars); exp._dValue = 8d + Math.floor(rand.nextDouble()*4); s._reward = exp;
		
		//RTDP algorithm proper:
		bestActionAtInit = null;
		doRTDP(currentState);
		
		String actionTaken = null;
		if(bestActionAtInit != null)
		{
			actionTaken = bestActionAtInit._string;
		}
		
		//Get a bridge between action names and their ArrayList<PVAR_INST_DEF> representation, to return a proper action.
		Map<String, ArrayList<PVAR_INST_DEF>> actionMap = ActionGenerator.getLegalBoolActionMap(s);
		
		//If no good action is found, do a random one: transform the Set into list and randomize a index...
		if (actionTaken == null) 
		{
			ArrayList<String> actions = new ArrayList<String>(actionMap.keySet());
			actionTaken = actions.get(rand.nextInt(actions.size()));
		} 
		
		remainingHorizon--;
		return actionMap.get(actionTaken);
	}

	/**
	 * This method executes a single RTDP trial and updates the best action found so far.
	 **/
	private void executeTrial(ArrayList initState) throws TimeOutException 
	{
		//Start trial with no selected actions, from initial state.
		CString bestAction = null;		
		ArrayList currState = initState;
				
		//Go to the horizon, choosing next states through coin toss and calculating the Q function
		for (int i = remainingHorizon; i > 0; i--)
		{
			//Flush caches and check time limit
			flushCaches();
			checkTimeLimit();

			//Find the best action for currState and compute Q
			QValue result = selectQValue(currState);
			if (bestAction == null)
			{
				bestActionAtInit = result.action;
				bestAction = result.action;
			}

			// Update Q
			valueOfDD = DDUtils.UpdateValue(context, valueOfDD, currState, result.qValue);
			
			//Sample next state (skip this in final step, small tweak)
			if (i > 1)
				currState = chooseNextState(currState, result.action);
		}
	}
	
	/**
	 * This method returns the best action and its perceived value for the current state (in a QValue instance).
	 * It does this by calculating Q for every viable action from the state given and selecting the best one.
	 **/
	private QValue selectQValue(ArrayList state) {

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
		context.addSpecialNode(valueOfDD);

		context.flushCaches(false);
	}
	
	private void checkTimeLimit() throws TimeOutException 
	{
		remainingHorizon = (int)Math.floor(SOLVER_TIME_LIMIT_PER_TURN);
		double elapsed_time = (System.currentTimeMillis() - startTime) / 1000;
		if (elapsed_time > SOLVER_TIME_LIMIT_PER_TURN)
			throw new TimeOutException("Time limit exceded.");
	}
}
