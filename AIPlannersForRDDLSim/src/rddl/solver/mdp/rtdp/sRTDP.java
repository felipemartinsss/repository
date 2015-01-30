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

import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;
import dd.discrete.DD;
import dd.discrete.ADD;

import rddl.*;
import rddl.RDDL.*;
import rddl.policy.Policy;
import rddl.policy.SPerseusSPUDDPolicy;
import rddl.solver.DDUtils;
import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Pair;

public class sRTDP extends Policy {
	
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
	public int _nGetActions=0;
	public int _nContUpperUpdates; //For computing the number of value function updates
	public HashMap<CString, Action> _hmActionName2Action; // Holds transition function
	
	// State variables
	public int _nRemainingHorizon = -1;
	
	// Just use the default random seed
	public Random _rand = new Random();
	public Double _nPercError = 0.7d;
	public Double _nErrorGen = 0d;
	public double base = 1.04648d;
	
	// Constructors
	public sRTDP() { }
	
	public sRTDP(String instance_name) {
		super(instance_name);
	}

	///////////////////////////////////////////////////////////////////////////
	//                      Main Action Selection Method
	///////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {		
		if (_nGetActions>4)
			_apply = true;
		//System.out.println("FULL STATE:\n\n" + SPerseusSPUDDPolicy.getStateDescription(s));
		//SOLVER_TIME_LIMIT_PER_TURN = Math.pow(1.04, _nRemainingHorizon);
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
		System.out.println("Number of VUpper Updates: "+_nContUpperUpdates);
		--_nRemainingHorizon; // One less action to take
		_nGetActions++;
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
	public double  _nTimeLimitSecs;
	public static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	public INSTANCE _rddlInstance = null;
	public int _valueDD;
	public int _nDDType; // Type of DD to use
	public int _nTrials;
	public int _nTapply;
	public double _dRewardRange; // Important if approximating
	public double _dDiscount;
	public int _nHorizon;
	public boolean _apply = false;
	public CString _csBestActionInitState = null;
	public HashMap<Integer,Integer> _hmPrimeVarID2VarID;
	public HashMap<String,String> _hmNonPrimeRemap;

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
		
		// In RTDP we need to map from CPT head var (primed) into non-prime state variable
		_hmPrimeVarID2VarID = new HashMap<Integer,Integer>();
		_hmNonPrimeRemap = new HashMap<String,String>();
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
			_hmNonPrimeRemap.put(var_prime, var);
		}
		
		_dRewardRange = 0d;
		for (Action a : _hmActionName2Action.values())
			_dRewardRange = Math.max(_dRewardRange, 
					_context.getMaxValue(a._reward) - 
			        _context.getMinValue(a._reward));
		
		// IMPORTANT: RTDP needs **optimistic upper bound initialization**
		double value_range = (_dDiscount < 1d) 
			? _dRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
			: _nHorizon * _dRewardRange;        // assume max reward over horizon
		_nErrorGen = Math.abs(value_range*_nPercError)/1000;
		_valueDD = _context.getConstantNode(value_range);
		System.out.println("Max:"+value_range);
		System.out.println("Error= " + _nErrorGen);
		//base = timeInstance();
	}

	// Main RTDP Algorithm
	public void doRTDP(double time_limit_secs, ArrayList init_state) {

		System.out.println("RTDP: Time limit: " + _nTimeLimitSecs + 
				" seconds, discount: " + _dDiscount + ", horizon: " + 
				_nRemainingHorizon + "/" + _nHorizon);

		_nTimeLimitSecs = time_limit_secs;
		_lStartTime = System.currentTimeMillis();
		//CString best_action_init_state = null;
		
		try {
			// Trial depth should be exactly equal to remaining horizon-to-go on this round
			_nTrials = 0;
			_nTapply = 0;
			while(/*_nTrials<1){/*/true) {
				doRTDPTrial(_nRemainingHorizon, init_state);
				_nTrials++;
				_nTapply++;
			}
		} catch (TimeOutException e) {
			System.out.println("RTDP: TIME LIMIT EXCEEDED after " + _nTrials + " trials.");
		} catch (Exception e) {
			System.err.println("RTDP: ERROR at " + _nTrials + " trials.");
			e.printStackTrace(System.err);
			System.exit(1);
		} finally {
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " + 
					_context.countExactNodes(_valueDD) + " nodes, best action: " + 
					_csBestActionInitState);
		}
		
		// Return the best action for the initial state from the last completed trial
		//return best_action_init_state == null ? null : best_action_init_state._string;
	}
	public int _Edd=0, _NEdd=0;
	// Run a single RTDP trial, return best action as seen from initial state
	public void doRTDPTrial(int trial_depth, ArrayList init_state) throws TimeOutException {
		/*if (_nTapply>1){
			_apply = true;
			_nTapply = 0;
		}
		else
			_apply = false;*/
		//CString best_action_init_state = null;
		CString best_action = null;
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		//ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>(_nTrials+1);
		for (int steps_to_go = _nTrials+3; steps_to_go > 0; steps_to_go--) {
			
			//System.out.println("Forward step [" + steps_to_go + "]: " + cur_state);
			
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			int valueEdd = 0;
			QUpdateResult res = null;
			_NEdd = _context.getConstantNode(1d);
			if (_apply){
				_Edd = _context.getConstantNode(0d);				
				ArrayList<Boolean> assign = new ArrayList<Boolean>();
				for (int i = 0; i <= _context._alOrder.size(); i++)
					assign.add(null);
				double val = _context.evaluate(_valueDD, cur_state);
				Generalize(_context.getNode(_valueDD), assign, val-_nErrorGen, val+_nErrorGen);
				//_context.getGraph(_valueDD).launchViewer();
				//_context.getGraph(_Edd).launchViewer();
				//_context.getGraph(_NEdd).launchViewer();
				//valueEdd = _context.applyInt(_valueDD, _Edd, DD.ARITH_PROD);
				//visited_states.add(cur_state);
				//_context.getGraph(valueEdd).launchViewer();
				// Compute best action for current state (along with Q-value to backup)
				int f = _context.getConstantNode(1d);
				res = getBestQValue(cur_state, _valueDD, f);//valueEdd, _Edd);//
			}
			else
				res = getBestQValue(cur_state, _valueDD, _NEdd);
			if (best_action == null){ // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
			}
			if (_apply){
				int f = _context.getConstantNode(res._dBestQValue);
				valueEdd = _context.applyInt(_Edd, f, DD.ARITH_PROD);
				//_context.getGraph(valueEdd).launchViewer();
				int valueNEdd = _context.applyInt(_valueDD, _NEdd, DD.ARITH_PROD);
				//_context.getGraph(valueNEdd).launchViewer();
				_valueDD = _context.applyInt(valueEdd, valueNEdd, DD.ARITH_SUM);
				//_context.getGraph(_valueDD).launchViewer();
				//_apply = false;
			}
			else
				_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			if (_nTrials>3){
				_apply = false;
				//_nTapply = 0;
			}
			// Update Q-value
			//_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			//Action a = _hmActionName2Action.get(res._csBestAction);
			//int suc = _context.remapGIDsInt(computeSuccesorsProbEnum(cur_state, a._hmVarID2CPT), _hmNonPrimeRemap);
			//toOneValue(_context.getNode(suc), _context.getDNode(1d, 1d, true));
			//int muldd = _context.applyInt(_valueDD, suc, DD.ARITH_PROD);
			//_context.getGraph(_valueDD).launchViewer();
			//_context.getGraph(suc).launchViewer();
			//_context.getGraph(muldd).launchViewer();
			_nContUpperUpdates++;
			// Sample next state
			cur_state = sampleNextState(cur_state, res._csBestAction);
		}
		
		// Do final updates *in reverse* on return
		/*for (int depth = visited_states.size() - 1; depth >= 0; depth--) {

			//System.out.println("Reverse step [" + depth + "]: " + cur_state);

			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();

			cur_state = visited_states.get(depth);

			// Update Q-value for each state
			QUpdateResult res = getBestQValue(cur_state);
			_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			_nContUpperUpdates++;
			// If back to initial state then update best action
			if (depth == 0) 
				_csBestActionInitState = res._csBestAction;
		}*/

		// All of the RTDP updates were just to find out best action from initial state
		// (as a byproduct, we've updated the value function via asychronous DP for
		//  reuse on the next step of this trial and other trials)
		//return best_action_init_state;
	}
	
	public static class QUpdateResult {
		public CString _csBestAction;
		public double  _dBestQValue;
		public QUpdateResult(CString best_action, double best_qvalue) {
			_csBestAction = best_action;
			_dBestQValue  = best_qvalue;
		}
	}

	// Find best Q-value/action for given state
	public QUpdateResult getBestQValue(ArrayList cur_state, int value, int edd) {
		
		int prime_vfun = _context.remapGIDsInt(value, _translation._hmPrimeRemap);

		QUpdateResult result = new QUpdateResult(null, -Double.MAX_VALUE); 
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			Action a = me.getValue();
			double qvalue = getQValue(prime_vfun, cur_state, a._csActionName, edd);
			if (result._csBestAction == null || qvalue > result._dBestQValue) { 
				result._csBestAction = a._csActionName;
				result._dBestQValue = qvalue;
			}
			//System.out.println("- " +a._csActionName + "(" + qvalue + ")");
		}
		//System.out.println("=> " + result._csBestAction + "(" + result._dBestQValue + ")");
		return result;
	}

	// Find Q-value for action in given state
	public double getQValue(int prime_vfun, ArrayList cur_state, CString action, int value) {
		
		Action a = _hmActionName2Action.get(action);
		
		// Find what gids (ADD level assignments of variables) are currently in vfun
		Set vfun_gids = _context.getGIDs(prime_vfun);

		// Show debug info if required
		if (VERBOSE_LEVEL >= 1) {
			System.out.println("Regressing action: " + a._csActionName + "\nGIDs: " + vfun_gids);
			System.out.println("Before sum out: " + _context.printNode(prime_vfun));
		}

		// Get CPT for each next state variable, restrict out current
		// state and multiply into dd_ret... result should be a constant
		// that is discounted, added to reward and returned

		//////////////////////////////////////////////////////////////
		// For each next-state variable in DBN for action 'a'
		//////////////////////////////////////////////////////////////
		for (Map.Entry<Integer, Integer> me : a._hmVarID2CPT.entrySet()) {
			
			int head_var_gid = me.getKey();
			int cpt_dd = me.getValue();
			
			// No need to regress variables not in the value function  
			if (!vfun_gids.contains(head_var_gid)) {
				if (VERBOSE_LEVEL >= 1) {
					System.out.println("Skipping " + _context._hmID2VarName.get(head_var_gid) + " / " + head_var_gid);
					System.out.println("... not in " + vfun_gids);
				}
				continue;
			}

			// For each CPT, evaluate in current state for next state variable true
			int level_prime = (Integer)_context._hmGVarToLevel.get(head_var_gid);
			cur_state.set(level_prime, true);
			double prob_true = _context.evaluate(cpt_dd, cur_state);
			if (Double.isNaN(prob_true)) {
				System.err.println("ERROR in RTDP.sampleNextState: Expected single value when evaluating: " + cur_state);
				//System.err.println("in " + context.printNode(cpt_dd));
				System.exit(1);
			}
			cur_state.set(level_prime, null); // Undo so as not to change current_state
			int restricted_cpt_dd = _context.getVarNode(head_var_gid, 1d - prob_true, prob_true);

			// Show debug info if required
			if (VERBOSE_LEVEL >= 2)
				System.out.println("  - Summing out: " + _context._hmID2VarName.get(head_var_gid));

			///////////////////////////////////////////////////////////////////
			// Multiply next state variable DBN into current value function
			///////////////////////////////////////////////////////////////////
			int prime_vfun1 = _context.applyInt(prime_vfun, restricted_cpt_dd, DD.ARITH_PROD);

			///////////////////////////////////////////////////////////////////
			// Sum out next state variable
			///////////////////////////////////////////////////////////////////
			int prime_vfun2 = _context.opOut(prime_vfun1, head_var_gid, DD.ARITH_SUM);
			prime_vfun = prime_vfun2;
		}
		
		if (VERBOSE_LEVEL >= 1) 
			System.out.println("After sum out: " + _context.printNode(prime_vfun));

		// Get action-dependent reward
		double exp_future_val = _context.evaluate(prime_vfun, (ArrayList)null) /* constant - no var assign needed */;
		double reward =0d;
		if (_apply){
			int newreward = _context.applyInt(a._reward, value, DD.ARITH_PROD);
			reward = _context.evaluate(newreward, cur_state);
		}
		else
			reward = _context.evaluate(a._reward, cur_state);
		
		// Return regressed value for current state
		return reward + _dDiscount * exp_future_val;
	}

	// For now we assume that the ADD transition functions for all
	// actions apply in every state... will have to revisit this later
	// w.r.t. RDDL's state-action constraints
	public ArrayList sampleNextState(ArrayList current_state, CString action) {
		
		Action a = _hmActionName2Action.get(action);
		ArrayList next_state = (ArrayList)current_state.clone(); // ensure correct size
		
		// Sample each next state variable to build a new state
		for (Map.Entry<Integer, Integer> me : a._hmVarID2CPT.entrySet()) {
			int prime_var_id = me.getKey();
			int cpt_dd = me.getValue();
			
			// For each CPT, evaluate in current state for next state variable true
			int level_prime = (Integer)_context._hmGVarToLevel.get(prime_var_id);
			current_state.set(level_prime, true);
			double prob_true = _context.evaluate(cpt_dd, current_state);
			if (Double.isNaN(prob_true)) {
				System.err.println("ERROR in RTDP.sampleNextState: Expected single value when evaluating: " + current_state);
				//System.err.println("in " + context.printNode(cpt_dd));
				System.exit(1);
			}
			current_state.set(level_prime, null); // Undo so as not to change current_state
			
			// Draw sample
			boolean is_true = _random.nextDouble() < prob_true; 
			
			// Assign truth value to level for unprimed variable
			int var_id = _hmPrimeVarID2VarID.get(prime_var_id);
			int level_unprime = (Integer)_context._hmGVarToLevel.get(var_id);
			next_state.set(level_unprime, is_true);
		}
		
		return next_state;
	}
		
	////////////////////////////////////////////////////////////////////////////
	// DD Cache Maintenance for MDPs
	////////////////////////////////////////////////////////////////////////////

	// Frees up memory... only do this if near limit?
	public void flushCaches() {
		if (!ALWAYS_FLUSH
				&& ((double) RUNTIME.freeMemory() / (double) RUNTIME
						.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			return; // Still enough free mem to exceed minimum requirements
		}

		_context.clearSpecialNodes();
		for (Integer dd : _allMDPADDs)
			_context.addSpecialNode(dd);
		_context.addSpecialNode(_valueDD);

		_context.flushCaches(false);
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
		SOLVER_TIME_LIMIT_PER_TURN=time;
	}
	
	public int getNumberUpdate() {
		return _nContUpperUpdates;
	}
	
	private int computeSuccesorsProbEnum(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
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
		return multCPTs;
	}
	
	public Integer toOneValue(ADDNode node, int leaf){
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;				
				Integer nL = toOneValue(_context.getNode(internalNode._nLow), leaf);
				if (nL != null)
					internalNode._nLow = nL;
				Integer nH = toOneValue(_context.getNode(internalNode._nHigh), leaf);
				if (nH != null)
					internalNode._nHigh = nH;
			} else if (node instanceof ADDDNode)				
				return	leaf;
		}
		return null;
	}
	
	public void Generalize(ADDNode node, ArrayList <Boolean> assign, double min, double max){
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				int level_var = (Integer)_context._hmGVarToLevel.get(internalNode._nTestVarID);
				assign.set(level_var, new Boolean(false));
				Generalize(lowNode, assign, min, max);
				assign.set(level_var, new Boolean(true));
				Generalize(highNode, assign, min, max);
				assign.set(level_var, null);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				if (probabilidade >=min && probabilidade<= max) {					
					ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
					newAssign.addAll(assign);					
					_Edd = DDUtils.UpdateValue(_context, _Edd, newAssign, 1d);
					_NEdd = DDUtils.UpdateValue(_context, _NEdd, newAssign, 0d);
				}
			}
		}
	}
	
	public double timeInstance(){
		int ind = _sInstanceName.indexOf("__");
		String domain = _sInstanceName.substring(0, ind);
		String instance = _sInstanceName.substring(ind+2, _sInstanceName.length());
		int indice = Integer.parseInt(instance) - 1;
		double[] navigation = {0.95,0.958,0.959,0.977,0.97,0.976,0.985,1.005,1.012,1.023};//1.0151,1.02
		//double[] navigation = {0.83,0.85,0.88,0.91,0.915,0.945,0.95,0.97,0.99,1.002};
		return navigation[indice];
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
