/**
 * RDDL: Factored RTDP Implementation.
 * 
 * @author Scott Sanner (ssanner [at] gmail.com)
 * @version 9/24/11
 *
 * For references on some of the underlying ideas, please see:
 *
 *   A. Barto, S. J. Bradtke, S. P. Singh.
 *   Learning to act using real-time dynamic programming.
 *   Artificial Intelligence.  72 (1-2), 81--138, 1995.
 * 
 *   Z. Feng, E. Hansen, S. Zilberstein.
 *   Symbolic generalization for on-line planning.
 *   UAI 2003.
 *
 * ./run rddl.sim.Simulator files/rddl/test/ rddl.solver.mdp.rtdp.RTDP sysadmin_test1 rddl.viz.SysAdminScreenDisplay
 **/

package rddl.solver.mdp.rtdp;

import graph.Graph;

import java.math.BigDecimal;
import java.text.DecimalFormat;
import java.util.*;

// import org.GNOME.Accessibility._ValueStub;


import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.DD;
import dd.discrete.ADD;
import dd.discrete.ADDNode;

import rddl.*;
import rddl.RDDL.*;
import rddl.policy.Policy;
import rddl.policy.SPerseusSPUDDPolicy;
import rddl.solver.DDUtils;
import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import rddl.solver.mdp.rtdp.RTDPEnum.ProbState;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Pair;

public class BRTDPEnum extends Policy {
	
	public static double SOLVER_TIME_LIMIT_PER_TURN = 1.2d; // Solver time limit (seconds)
	
	public final static boolean SHOW_STATE   = true;
	public final static boolean SHOW_ACTIONS = true;
	public final static boolean SHOW_ACTION_TAKEN = true;
	
	// Only for diagnostics, comment this out when evaluating
	public final static boolean DISPLAY_SPUDD_ADDS_GRAPHVIZ = false;
	public final static boolean DISPLAY_SPUDD_ADDS_TEXT = false;
	
	public RDDL2Format _translation = null;
	
	// Using CString wrapper to speedup hash lookups
	public ADD _context;
	public ArrayList<Integer> _allMDPADDs;
	public ArrayList<CString> _alStateVars;
	public ArrayList<CString> _alPrimeStateVars;
	public ArrayList<CString> _alActionNames;
	public int _nContUpperUpdates;
	public HashMap<CString, Action> _hmActionName2Action; // Holds transition function
	public ArrayList _alAssign;
	public int _nProf=5;
	public double base = 1.04648d;
	
	// State variables
	public int _nRemainingHorizon = -1;
	
	// Just use the default random seed
	public Random _rand = new Random();
		
	// Constructors
	public BRTDPEnum() { }
	
	public BRTDPEnum(String instance_name) {
		super(instance_name);
	}

	///////////////////////////////////////////////////////////////////////////
	//                      Main Action Selection Method
	///////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
		//System.out.println("FULL STATE:\n\n" + SPerseusSPUDDPolicy.getStateDescription(s));
		//SOLVER_TIME_LIMIT_PER_TURN = Math.pow(1.05, _nRemainingHorizon);
		SOLVER_TIME_LIMIT_PER_TURN = Math.pow(base,base>=1?_nRemainingHorizon: _nHorizon- _nRemainingHorizon+1)/3;
		if (s == null) {
			// This should only occur on the **first step** of a POMDP trial
			System.err.println("ERROR: NO STATE/OBS: MDP must have state.");
			System.exit(1);
		}
		
		// Get a set of all true observation or state variables
		TreeSet<CString> true_vars = 
			CString.Convert2CString(SPerseusSPUDDPolicy.getTrueFluents(s, "states"));
		if (SHOW_STATE) {
			System.out.println("\n==============================================");
			System.out.println("\nTrue state variables:");
			for (CString prop_var : true_vars)
				System.out.println(" - " + prop_var);
		}
		
		// Get a map of { legal action names -> RDDL action definition }  
		Map<String,ArrayList<PVAR_INST_DEF>> action_map = 
			ActionGenerator.getLegalBoolActionMap(s);
		
		// RTDP algorithm
		//
		// Everytime we reach a state, do a number of trials starting from this
		// state and going to end of horizon.  At each step of trial, compute
		// local backups and in the process the best action (especially
		// keep track of for starting state).  Use trick to evaluate then
		// correct ADD for ADD value update.
		
		// Use the precomputed q-functions (cached when the value function
		// was computed) to determine the best action for this state
		ArrayList add_state_assign = DDUtils.ConvertTrueVars2DDAssign(_context, true_vars, _alStateVars);
		_csBestActionInitState = null;
		doRTDP(SOLVER_TIME_LIMIT_PER_TURN, add_state_assign);
		String action_taken = (_csBestActionInitState == null? null: _csBestActionInitState._string);
		if (action_taken == null) {
			// No RTDP results available, just take random action
			ArrayList<String> actions = new ArrayList<String>(action_map.keySet());
			action_taken = actions.get(_rand.nextInt(actions.size()));
			if (SHOW_ACTION_TAKEN)
				System.out.println("\n--> [Random] action taken: " + action_taken);
		} else if (SHOW_ACTION_TAKEN)
			System.out.println("\n--> [RTDP] best action taken: " + action_taken);
		System.out.println("Number of Vupper Updates:" + _nContUpperUpdates);
		--_nRemainingHorizon; // One less action to take
		return action_map.get(action_taken);
	}

	///////////////////////////////////////////////////////////////////////////
	//                         Round / Session Signals
	//
	// If you need to keep track of state information across rounds or sessions, 
	// just modify these methods.  (Each session consists of total_rounds rounds.)
	///////////////////////////////////////////////////////////////////////////

	public void roundInit(double time_left, int horizon, int round_number, int total_rounds) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> ROUND INIT " + round_number + "/" + total_rounds + "; time remaining = " + time_left + ", horizon = " + horizon);
		System.out.println("*********************************************************");
				
		// Reset horizon
		_nRemainingHorizon = horizon;
		_nContUpperUpdates = 0;
		// Build ADDs for transition, reward and value function (if not already built)
		if (_translation == null) {
			
			// Use RDDL2Format to build SPUDD ADD translation of _sInstanceName
			try {
				_translation = new RDDL2Format(_rddl, _sInstanceName, RDDL2Format.SPUDD_CURR, "");
			} catch (Exception e) {
				System.err.println("Could not construct MDP for: " + _sInstanceName + "\n" + e);
				e.printStackTrace(System.err);
				System.exit(1);
			}

			// Get ADD context and initialize value function ADD
			_allMDPADDs = new ArrayList<Integer>();
			_context = _translation._context;

			// Get the state var and action names
			_alStateVars = new ArrayList<CString>();
			_alPrimeStateVars = new ArrayList<CString>();
			for (String s : _translation._alStateVars) {
				_alStateVars.add(new CString(s));
				_alPrimeStateVars.add(new CString(s + "'"));
			}
			
			_alActionNames = new ArrayList<CString>();
			for (String a : _translation._hmActionMap.keySet())
				_alActionNames.add(new CString(a));
			//_hmReward = new HashMap<CString, HashMap<ArrayList,Double>>();
			// Now extract the reward and transition ADDs
			_hmActionName2Action = new HashMap<CString,Action>();
			for (String a : _translation._hmActionMap.keySet()) {
				HashMap<CString,Integer> cpts = new HashMap<CString,Integer>();
				int reward = _context.getConstantNode(0d);
				
				// Build reward from additive decomposition
				ArrayList<Integer> reward_summands = _translation._act2rewardDD.get(a);
				for (int summand : reward_summands)
					reward = _context.applyInt(reward, summand, ADD.ARITH_SUM);
				_allMDPADDs.add(reward);
				// Build CPTs
				for (String s : _translation._alStateVars) {
					int dd = _translation._var2transDD.get(new Pair(a, s));
					
					int dd_true  = _context.getVarNode(s + "'", 0d, 1d);
					dd_true = _context.applyInt(dd_true, dd, ADD.ARITH_PROD);
		
					int dd_false = _context.getVarNode(s + "'", 1d, 0d);
					//System.out.println("Multiplying..." + dd + ", " + DD_ONE);
					//_context.printNode(dd);
					//_context.printNode(DD_ONE);
					int one_minus_dd = _context.applyInt(_context.getConstantNode(1d), dd, ADD.ARITH_MINUS);
					dd_false = _context.applyInt(dd_false, one_minus_dd, ADD.ARITH_PROD);
					
					// Now have "dual action diagram" cpt DD
					int cpt = _context.applyInt(dd_true, dd_false, ADD.ARITH_SUM);

					cpts.put(new CString(s + "'"), cpt);
					_allMDPADDs.add(cpt);
				}
				
				// Build Action and add to HashMap
				CString action_name = new CString(a);
				Action action = new Action(_context, action_name, cpts, reward);
				_hmActionName2Action.put(action_name, action);
			}
			
			// Display ADDs on terminal?
			if (DISPLAY_SPUDD_ADDS_TEXT) {
				System.out.println("State variables: " + _alStateVars);
				System.out.println("Action names: " + _alActionNames);
				
				for (CString a : _alActionNames) {
					Action action = _hmActionName2Action.get(a);
					System.out.println("Content of action '" + a + "'\n" + action);
				}
			}
			
			// Display ADDs in graph visualization window?
			// (only show a subset... 100's to display otherwise)
			final int MAX_DISPLAY = 10;
			if (DISPLAY_SPUDD_ADDS_GRAPHVIZ) {
				int displayed = 0;
				for (CString a : _alActionNames) {
					Action action = _hmActionName2Action.get(a);
					
					// Show cpts for each action/var
					for (CString var : _alStateVars) {
						_context.getGraph(action._hmStateVar2CPT.get(var)).launchViewer();

						if (++displayed >= MAX_DISPLAY)
							break;
					}
					
					// Show reward for action
					_context.getGraph(action._reward).launchViewer();
					
					if (++displayed >= MAX_DISPLAY)
						break;
				}				
			}
			
			// Initialize RTDP solver
			resetSolver();
		}
		
		_nRemainingHorizon = _nHorizon;
	}
	
	public void roundEnd(double reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out.println("*********************************************************");
		
		//_context.getGraph(_valueDD).launchViewer(1300, 770);
	}
	
	public void sessionEnd(double total_reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> SESSION END, total reward = " + total_reward);
		System.out.println("*********************************************************");
	}
	
	///////////////////////////////////////////////////////////////////////////
	//                      Factored Value Iteration Solver
	///////////////////////////////////////////////////////////////////////////
	
	// Local constants
	public final static int VERBOSE_LEVEL = 0; // Determines how much output is displayed
	
	public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush until < this amt

	// For printing
	public final static DecimalFormat _df = new DecimalFormat("#.###");

	// Timing variables
	public long _lStartTime; // For timing purposes
	public double _nTimeLimitSecs;
	public static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	public INSTANCE _rddlInstance = null;
	public HashMap<ArrayList<Boolean>,Double> _VUpper, _VLower;
	public int _nDDType; // Type of DD to use
	public int _nTrials;
	public double _dRewardRange; // Important if approximating
	public double _dMinRewardRange;
	public double _dDiscount;
	public ArrayList _InitialState;
	public double gapInitial;
	public CString _csBestActionInitState = null;
	public double _Tau;
	public Boolean _firstTime;
	public int _nHorizon;
	public HashMap<Integer, Pair<Double, Double>> _hmNodeWeight;//weights for lower and upper branch Vgap
	public HashMap<Integer,Integer> _hmPrimeVarID2VarID;
	private double maxUpperUpdated,maxLowerUpdated;
	public HashMap<CString,HashMap<ArrayList,Double>> _hmReward;
	public double _nProbAcum;

	// Initialize all variables (call before starting value iteration)
	public void resetSolver() {
		_nTrials = -1;
		_rddlInstance = _rddl._tmInstanceNodes.get(this._sInstanceName);
		if (_rddlInstance == null) {
			System.err.println("ERROR: Could not fine RDDL instance '" + _rddlInstance + "'");
			System.exit(1);
		}
		_dDiscount = _rddlInstance._dDiscount;
		if (_dDiscount == 1d)
			_dDiscount = 0.99d;
		_nHorizon  = _rddlInstance._nHorizon;
		_Tau = 40;
		// In RTDP we need to map from CPT head var (primed) into non-prime state variable
		_hmPrimeVarID2VarID = new HashMap<Integer,Integer>();
		for (Map.Entry<String, String> me : _translation._hmPrimeRemap.entrySet()) {
			String var = me.getKey();
			String var_prime = me.getValue();
			Integer var_id = (Integer)_context._hmVarName2ID.get(var);
			Integer var_prime_id = (Integer)_context._hmVarName2ID.get(var_prime);
			if (var_id == null || var_prime_id == null) {
				System.err.println("ERROR: Could not get var IDs " 
						+ var_id + "/" + var_prime_id
						+ " for " + var + "/" + var_prime);
				System.exit(1);
			}
			_hmPrimeVarID2VarID.put(var_prime_id, var_id);
		}
		
		_dRewardRange = -Double.MAX_VALUE;
		_dMinRewardRange = Double.MAX_VALUE;
		for (Action a : _hmActionName2Action.values()){
			double MinValue = _context.getMinValue(a._reward); 
			_dRewardRange = Math.max(_dRewardRange, 
					_context.getMaxValue(a._reward) - 
			        MinValue);
			_dMinRewardRange = Math.min(_dMinRewardRange, MinValue);
		}
		// IMPORTANT: RTDP needs **optimistic upper bound initialization**
		/*double value_range = (_dDiscount < 1d) 
			? _dRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
			: _nHorizon * _dRewardRange;        // assume max reward over horizon
		double min_value_range = (_dDiscount < 1d) 
			? _dMinRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
			: _nHorizon * _dMinRewardRange;        // assume max reward over horizon*/
		_VUpper = new HashMap<ArrayList<Boolean>, Double>();
		_VLower = new HashMap<ArrayList<Boolean>, Double>();
	}

	private ArrayList remapWithPrimes(ArrayList nextState) {
		ArrayList state = new ArrayList();
		for (int j = 0; j< nextState.size();j++)
			state.add(null);
		for (int i = 0; i< nextState.size();i++){        			
			Object val = nextState.get(i);
			if(val != null)	{
				int id = (Integer)_context._alOrder.get(i);
				int idprime = (Integer)_context._hmGVarToLevel.get(_context._hmVarName2ID.get(_translation._hmPrimeRemap.get(_context._hmID2VarName.get(id))));
				state.set(idprime, val);
			}
		}
		return state;
	}
	
	
	private ArrayList samplingVGap(Integer beginF) {
		ArrayList assign = new ArrayList();
		for (int i = 0; i <= _context._alOrder.size(); i++)
			assign.add(null);
		Integer F=beginF;
		for (CString s : _alStateVars) {
			double ran=_random.nextDouble();
			Integer index = (Integer)_context._hmVarName2ID.get(s._string); // if null, var not in var2ID
			Integer level = (Integer)_context._hmGVarToLevel.get(index);
			ADDNode Node =_context.getNode(F);
			if(Node instanceof ADDINode){
				ADDINode intNodeKey=(ADDINode)Node;
				Integer Fvar= intNodeKey._nTestVarID;
				if(Fvar.compareTo(index)==0){ //var is in the ADD
					Pair<Double, Double> pair = _hmNodeWeight.get(F);
					double wH=pair._o1;
					double wL=pair._o2;
					Boolean condition = ran>(wL/(wH + wL));
					assign.set(level,condition);
					if (condition)
						F=intNodeKey._nHigh;					
					else
						F=intNodeKey._nLow;
				}
				else //var is not in the ADD sample equality
					assign.set(level,ran>0.5);
			}
			else //is terminal node and there are more state variables to sample
				assign.set(level,ran>0.5);
		}
		return assign;
	}
	
	/*private void updateVLower(ArrayList state) {
		double max=Double.NEGATIVE_INFINITY;
		for (CString actionName:_alActionNames){			
			double Qt = getQValue(_VLower,state,actionName);
			max=Math.max(max,Qt);
		}
	    //update the ADD
		_VLower = DDUtils.UpdateValue(_context, _VLower, state, max);
		maxLowerUpdated=max;
	}*/

	// Main RTDP Algorithm
	public void doRTDP(double time_limit_secs, ArrayList init_state) {

		System.out.println("RTDP: Time limit: " + _nTimeLimitSecs + 
				" seconds, discount: " + _dDiscount + ", horizon: " + 
				_nRemainingHorizon + "/" + _nHorizon);

		_nTimeLimitSecs = time_limit_secs;
		_lStartTime = System.currentTimeMillis();
		_InitialState = init_state;
		
		try {
			// Trial depth should be exactly equal to remaining horizon-to-go on this round
			_nTrials = 0;
			while(true) {
				doRTDPTrial(_nRemainingHorizon, init_state);
				_nTrials++;
			}
		} catch (TimeOutException e) {
			System.out.println("RTDP: TIME LIMIT EXCEEDED after " + _nTrials + " trials.");
		} catch (Exception e) {
			System.err.println("RTDP: ERROR at " + _nTrials + " trials.");
			e.printStackTrace(System.err);
			System.exit(1);
		} finally {
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " /*+ 
					_context.countExactNodes(_VUpper)*/ + " nodes, best action: " + 
					_csBestActionInitState);
		}
		
		// Return the best action for the initial state from the last completed trial
		//return best_action_init_state == null ? null : best_action_init_state._string;
	}
	
	// Run a single RTDP trial, return best action as seen from initial state
	public void doRTDPTrial(int trial_depth, ArrayList init_state) throws TimeOutException {
			
		_firstTime = true;
		CString best_action = null;
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>(_nTrials + 1);
		for (int steps_to_go = _nTrials + 1; steps_to_go > 0 && cur_state != null; steps_to_go--) {
			
			//System.out.println("Forward step [" + steps_to_go + "]: " + cur_state);
			
			// Flush caches and check time limit
			//flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();

			visited_states.add(cur_state);
			
			// Compute best action for current state (along with Q-value to backup)
			QUpdateResult resU = getBestQValue(cur_state,_VUpper, _dRewardRange);
			QUpdateResult resL = getBestQValue(cur_state, _VLower, _dMinRewardRange);
			if (best_action == null){ // first time through will update
				_csBestActionInitState = resU._csBestAction;
				best_action = _csBestActionInitState;
			}
			// Update Q-value
			if(_VUpper.containsKey(cur_state))
				_VUpper.remove(cur_state);
			_VUpper.put(cur_state, resU._dBestQValue);
			_nContUpperUpdates++;
			if(_VLower.containsKey(cur_state))
				_VLower.remove(cur_state);
			_VLower.put(cur_state, resL._dBestQValue);
			//long inicio = System.currentTimeMillis();
			//_VGap = DDUtils.UpdateValue(_context, _VGap, cur_state, resU._dBestQValue - resL._dBestQValue);
			//System.out.println("Update: "+ (System.currentTimeMillis()-inicio));
			// Sample next state
			//inicio = System.currentTimeMillis();
			cur_state = SortearEstado(resU._alProbEstados);
			//System.out.println("Sampĺe: "+ (System.currentTimeMillis()-inicio));
		}
		
		// Do final updates *in reverse* on return
		for (int depth = visited_states.size() - 1; depth >= 0; depth--) {

			//System.out.println("Reverse step [" + depth + "]: " + cur_state);

			// Flush caches and check time limit
			//flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();

			cur_state = visited_states.get(depth);

			// Update Q-value for each state
			QUpdateResult resU = getBestQValue(cur_state,_VUpper, _dRewardRange);
			QUpdateResult resL = getBestQValue(cur_state, _VLower, _dMinRewardRange);
			if(_VUpper.containsKey(cur_state))
				_VUpper.remove(cur_state);
			_VUpper.put(cur_state, resU._dBestQValue);
			_nContUpperUpdates++;
			if(_VLower.containsKey(cur_state))
				_VLower.remove(cur_state);
			_VLower.put(cur_state, resL._dBestQValue);
			
			//IMPORTANT: for BRTDP you use the VLower to do the simulations
			// If back to initial state then update best action
			if (depth == 0) 
				_csBestActionInitState = resL._csBestAction;
		}

		// All of the RTDP updates were just to find out best action from initial state
		// (as a byproduct, we've updated the value function via asychronous DP for
		//  reuse on the next step of this trial and other trials)
		//return best_action_init_state;
	}
	
	public static class QUpdateResult {
		public CString _csBestAction;
		public double  _dBestQValue;
		public ArrayList<ProbState> _alProbEstados;
		public QUpdateResult(CString best_action, double best_qvalue, ArrayList<ProbState> ProbEstados) {
			_csBestAction = best_action;
			_dBestQValue  = best_qvalue;
			_alProbEstados = ProbEstados;
		}
	}

	// Find best Q-value/action for given state
	public QUpdateResult getBestQValue(ArrayList cur_state,HashMap<ArrayList<Boolean>, Double> prime_vfun, double valuebound) {
		QUpdateResult result = new QUpdateResult(null, -Double.MAX_VALUE, new ArrayList<ProbState>()); 
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			Action a = me.getValue();
			Pair<Double, ArrayList<ProbState>> qvalue = getQValue(prime_vfun, cur_state, a._csActionName, valuebound);
			if (result._csBestAction == null || qvalue._o1 > result._dBestQValue) { 
				result._csBestAction = a._csActionName;
				result._dBestQValue = qvalue._o1;
				result._alProbEstados =  qvalue._o2;
			}
			//System.out.println("- " +a._csActionName + "(" + qvalue + ")");
		}
		//System.out.println("=> " + result._csBestAction + "(" + result._dBestQValue + ")");
		return result;
	}

	// Find Q-value for action in given state
	public Pair<Double, ArrayList<ProbState>> getQValue(HashMap<ArrayList<Boolean>, Double> prime_vfun, ArrayList cur_state, CString action, Double valuebound) {
		
		Action a = _hmActionName2Action.get(action);
		
		// Find what gids (ADD level assignments of variables) are currently in vfun
		ArrayList<ProbState> ProbsStates= computeSuccesorsProbEnum(cur_state, a._hmVarID2CPT);
		
		//////////////////////////////////////////////////////////////
		// For each next-state variable in DBN for action 'a'
		//////////////////////////////////////////////////////////////
		double soma = 0;
		for (int indice =0;indice<ProbsStates.size()-1; indice++) {
			ProbState pS = ProbsStates.get(indice);
			if (!prime_vfun.containsKey(pS._alState))
				prime_vfun.put(pS._alState, valuebound);//_context.evaluate(a._reward, cur_state));
			double valor = prime_vfun.get(pS._alState);
			double prob = pS._dProb - ProbsStates.get(indice + 1)._dProb; 
			soma += (prob*valor);
		}
		// Get action-dependent reward
		double reward = _context.evaluate(a._reward, cur_state);
		// Return regressed value for current state
		return new Pair<Double, ArrayList<ProbState>>(reward + _dDiscount * soma, ProbsStates);
	}
	
	public Double setProbWeightVGap(Integer F,ArrayList state, HashMap<Integer, Integer> iD2ADD) {
		// TODO: if F is not dirty, just return without updating further
		//       make sure to mark node as not dirty after update
		
		ADDNode Node = _context.getNode(F);
	   	if(Node instanceof ADDDNode){
	   		//ADDDNode node=(ADDDNode)Node;
	   		//node.setprobWeightH(node.getValue());
	   		//node.setprobWeightL(0);
	   		return _context.evaluate(F, (ArrayList)null);
    	}
    	if(!_hmNodeWeight.containsKey(F)){
     		ADDINode intNodeKey=(ADDINode)Node;
     		Double highWeight = setProbWeightVGap(intNodeKey._nHigh,state,iD2ADD);
     		Double lowWeight = setProbWeightVGap(intNodeKey._nLow,state,iD2ADD);
     		String old_str = (String)_context._hmID2VarName.get(intNodeKey._nTestVarID);
			String new_str = (String)_translation._hmPrimeRemap.get(old_str);
			Integer new_id = null;
			if (new_str == null)
				new_id = intNodeKey._nTestVarID;
			else
				new_id = (Integer)_context._hmVarName2ID.get(new_str);
    		Integer cpt_a_xiprime=iD2ADD.get(new_id);
    		if(cpt_a_xiprime==null){
    			System.out.println("Prime var not found");
    			System.exit(1);
    		}
    		int level_prime = (Integer)_context._hmGVarToLevel.get(new_id);
			state.set(level_prime, true);
    		double probTrue=_context.evaluate(cpt_a_xiprime,state);
    		state.set(level_prime, null);
			double probFalse=1-probTrue;
			double weightH=probTrue*(highWeight);
			double weightL=probFalse*(lowWeight);
    		_hmNodeWeight.put(F, new Pair<Double, Double>(weightH, weightL));
    		return weightH+weightL;
    	}
    	else{
    		Pair<Double, Double> pair = _hmNodeWeight.get(F); 
    		return pair._o1+pair._o2;
    	}
	}

	// For now we assume that the ADD transition functions for all
	// actions apply in every state... will have to revisit this later
	// w.r.t. RDDL's state-action constraints
	/*public ArrayList sampleNextState(ArrayList current_state, CString action) {
		
		Action a = _hmActionName2Action.get(action);
		_hmNodeWeight = new HashMap<Integer, Pair<Double,Double>>();
		//	compute B
		Double B = setProbWeightVGap(_VGap, current_state, a._hmVarID2CPT);
		//System.out.println(_hmNodeWeight);
		//_context.getGraph(_VGap).launchViewer();
		//	check end trial/////////////////////
		ADDNode Node = _context.getNode(_VGap);
		if(Node instanceof ADDINode){
			// could precompute and store gInitial for each trial
			if (_firstTime){
				gapInitial=_context.evaluate((Integer)_VGap, _InitialState);
				_firstTime = false;
			}
			if(B< gapInitial/_Tau){
				return null;
			}
		}
		//sampling each state variable from top to bottom using the weighted probabilities
		return samplingVGap(_VGap);
	}*/
		
	////////////////////////////////////////////////////////////////////////////
	// DD Cache Maintenance for MDPs
	////////////////////////////////////////////////////////////////////////////

	// Frees up memory... only do this if near limit?
	/*public void flushCaches() {
		if (!ALWAYS_FLUSH
				&& ((double) RUNTIME.freeMemory() / (double) RUNTIME
						.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			return; // Still enough free mem to exceed minimum requirements
		}

		_context.clearSpecialNodes();
		for (Integer dd : _allMDPADDs)
			_context.addSpecialNode(dd);
		_context.addSpecialNode(_VUpper);
		_context.addSpecialNode(_VLower);
		_context.addSpecialNode(_VGap);

		_context.flushCaches(false);
	}*/
	private ArrayList<ProbState> computeSuccesorsProbEnum(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
		Integer multCPTs=_context.getConstantNode(1d);
		Integer xiprime;
		for (CString x : _alStateVars){		
			xiprime=(Integer)_context._hmVarName2ID.get(_translation._hmPrimeRemap.get(x._string));
			Integer cpt_a_xiprime = iD2ADD.get(xiprime);
			double probTrue,probFalse;
			int levelprime = (Integer)_context._hmGVarToLevel.get(xiprime);
			state.set(levelprime, true);
			probTrue=_context.evaluate(cpt_a_xiprime,state);
			state.set(levelprime, null);
			probFalse = 1 - probTrue;
			Integer Fh=_context.getConstantNode(probTrue);
			Integer Fl=_context.getConstantNode(probFalse);
			Integer newCPT = _context.getINode(xiprime, Fl, Fh, true);
			multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
		}
		ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		for (int i = 0; i <= _context._alOrder.size(); i++)
			assign.add(null);
		_nProbAcum = 0;
		inOrderSearch(_context.getNode(multCPTs), assign, alEstadoProb);
		for (ProbState ps : alEstadoProb)		
			ps._dProb = ps._dProb/_nProbAcum;		
		alEstadoProb.get(0)._dProb = 1;
		alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		return alEstadoProb;
	}
	
	public void inOrderSearch (ADDNode node, ArrayList <Boolean> assign, ArrayList<ProbState> alEstadoProb){
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				int id_var_prime = _hmPrimeVarID2VarID.get(internalNode._nTestVarID);
				int level_var = (Integer)_context._hmGVarToLevel.get(id_var_prime);
				assign.set(level_var, new Boolean(false));
				// Expande a subárvore low
				inOrderSearch (lowNode, assign, alEstadoProb);
				assign.set(level_var, new Boolean(true));
				// Expande a subárvore high
				inOrderSearch (highNode, assign, alEstadoProb);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de serem alcançados
				if (probabilidade > 0.0d) {
					ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
					newAssign.addAll(assign);
					if (!_VUpper.containsKey(newAssign))
						_VUpper.put(newAssign, _dRewardRange);
					if (!_VLower.containsKey(newAssign))
						_VLower.put(newAssign, _dMinRewardRange);
					double newValue = probabilidade*(_VUpper.get(newAssign) - _VLower.get(newAssign));
					ProbState novoNo = new ProbState(newValue, newAssign);
					_nProbAcum+= newValue;
					alEstadoProb.add(0, novoNo);
				}
			}
		}
	}
	
	public void TakeReward(ADDNode node, ArrayList <Boolean> assign, HashMap<ArrayList,Double> rew){
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				//int id_var_prime = _hmPrimeVarID2VarID.get(internalNode._nTestVarID);
				int level_var = (Integer)_context._hmGVarToLevel.get(internalNode._nTestVarID);
				assign.set(level_var, new Boolean(false));
				// Expande a subárvore low
				TakeReward(lowNode, assign, rew);
				assign.set(level_var, new Boolean(true));
				// Expande a subárvore high
				TakeReward(highNode, assign, rew);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				// Adiciona apenas os estados com probabilidade maior que de serem alcançados
				ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
				newAssign.addAll(assign);
				rew.put(newAssign, leaf._dLower);
			}
		}
	}

	public ArrayList<Boolean> SortearEstado(ArrayList<ProbState> alEstadoProb) {
		int inicio = 0;
		int fin = alEstadoProb.size()-2;
		int mitade = (fin+inicio)/2;
		Random alNumber = new Random();
		double rand = alNumber.nextDouble();
		ProbState upper = alEstadoProb.get(mitade);
		ProbState lower = alEstadoProb.get(mitade + 1);
		int indice = 0;
		while((rand > upper._dProb || rand <= lower._dProb) && fin-inicio>1){
			if (indice>15)
				System.out.println(indice);
			if (rand > upper._dProb)
				fin = mitade;
			else
				inicio =  mitade;
			mitade = (fin+inicio)/2;
			upper = alEstadoProb.get(mitade);
			lower = alEstadoProb.get(mitade + 1);
			indice++;
		}
		return upper._alState;
	}

	////////////////////////////////////////////////////////////////////////////
	// Miscellaneous helper methods
	////////////////////////////////////////////////////////////////////////////

	public void checkTimeLimit() throws TimeOutException {
		double elapsed_time = (System.currentTimeMillis() - _lStartTime) / 1000d;
		if (elapsed_time > (double)_nTimeLimitSecs)
			throw new TimeOutException("Elapsed time " + elapsed_time + " (s) exceeded time limit of " + _nTimeLimitSecs + " (s)");
	}
	
	public static String MemDisplay() {
		long total = RUNTIME.totalMemory();
		long free = RUNTIME.freeMemory();
		return total - free + ":" + total;
	}	
	
	public void setLimitTime(Integer time) {
		SOLVER_TIME_LIMIT_PER_TURN = time;
	}
	public int getNumberUpdate() {
		return _nContUpperUpdates;
	}
	///////////////////////////////////////////////////////////////////////
	// Notes on RDDL translation and how it affects RTDP/other algorithms:
	//
	// RDDL2Format's SPUDD translation enforces that only legal
	// joint actions are generated if the problem is concurrent
	// * need to think about how concurrent translation will work
	//
	// In future will need to generate masks for legal actions
	// and states:
	//
	// * the translator currently *ignores* whether actions
	// are not legal in certain states (generic ADD transition
	// does not know this)... two choices
	// - need a legal action mask for states
	// - never define joint state-action constraints
	//
	// * state constraints like (robot only in one location)
	// are currently *ignored* and lead to inefficiency for
	// algorithms like VI where initial state information not
	// exploited (really need to generate a legal state mask)
	///////////////////////////////////////////////////////////////////////
}
