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

//import javax.swing.text.html.HTMLDocument.Iterator;

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
//import rddl.solver.mdp.rtdp.LRTDP1.QUpdateResult;
import rddl.solver.mdp.rtdp.RTDPEnum.ProbState;
// import rddl.solver.mdp.rtdp.sRTDP_prunning_modif_0_03.PrunningNode;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Pair;

public class afactoredLRTDP_ave extends Policy {
	
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
	public int _nContUpperUpdates; //For computing the number of value function updates
	public HashMap<CString, Action> _hmActionName2Action; // Holds transition function
	//public ArrayList<ArrayList> _lSolvedStates = new ArrayList<ArrayList>();
	public ArrayList<Integer> _alSaveNodes; // Nodes to save during cache flushing
	
	// State variables
	public int _nRemainingHorizon = -1;
	
	// Just use the default random seed
	public Random _rand = new Random();
	public double _nEpsilon = 0.1;
	public double base = 1.04648d;
	public double _nmergeError = 0d;
	public double _ndelta = 0.03d;
	public int _nGetActions = 0;
	
	// Constructors
	public afactoredLRTDP_ave() { }
	
	public afactoredLRTDP_ave(String instance_name) {
		super(instance_name);
	}

	///////////////////////////////////////////////////////////////////////////
	//                      Main Action Selection Method
	///////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		if (_nGetActions>1)
			prune(_nmergeError);
		//System.out.println("FULL STATE:\n\n" + SPerseusSPUDDPolicy.getStateDescription(s));
		//SOLVER_TIME_LIMIT_PER_TURN = Math.pow(1.04, _nRemainingHorizon);
		SOLVER_TIME_LIMIT_PER_TURN = Math.pow(base,base>=1?_nRemainingHorizon: _nHorizon- _nRemainingHorizon+1)/3;
		_nGetActions++;
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
			_nSolvedADD = _context.getConstantNode(0);
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
	
	public void prune(double mergeerror){
		_valueDD = pruneNodesValue(_valueDD, mergeerror);
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
	public double _dRewardRange; // Important if approximating
	public double _dValueRange; // Important if approximating
	public double _dDiscount;
	public int _nHorizon;
	public Stack<Integer> _sOpen;
	public CString _csBestActionInitState = null;
	public HashMap<Integer,Integer> _hmPrimeVarID2VarID;
	public HashMap<Integer,Integer> _hmVarID2PrimeVarID;
	//ArrayList<ArrayList> _alGoalStates = new ArrayList<ArrayList>();
	public int _nSolvedADD = 0;
	public Hashtable reduceRemapLeavesCache;
	
	public int _nE;
	public int _nMaskedE;
	public int _nmaxDD;
	public int _nOpenAdd;
	public int _nClosedAdd;
	public int _nClosed;

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
		_alSaveNodes  = new ArrayList<Integer>();
		// In RTDP we need to map from CPT head var (primed) into non-prime state variable
		_hmPrimeVarID2VarID = new HashMap<Integer,Integer>();
		_hmVarID2PrimeVarID = new HashMap<Integer,Integer>();
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
			_hmVarID2PrimeVarID.put(var_id, var_prime_id);
		}
		
		_dRewardRange = 0d;
		for (Action a : _hmActionName2Action.values()){
			_dRewardRange = Math.max(_dRewardRange, 
					_context.getMaxValue(a._reward) - 
			        _context.getMinValue(a._reward));
			ArrayList state = new ArrayList();
			for (int i = 0; i <= _context._alOrder.size(); i++)
				state.add(i<_alStateVars.size()? false: null);			
			//MaxState(a._reward, state);			
		}
		
		// IMPORTANT: RTDP needs **optimistic upper bound initialization**
		double value_range = (_dDiscount < 1d) 
			? _dRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
			: _nHorizon * _dRewardRange;        // assume max reward over horizon
		_dValueRange = _dRewardRange;
		_nmergeError = Math.abs(value_range*_ndelta);
		System.out.println("Max:"+value_range);
		_valueDD = _context.getConstantNode(_dRewardRange);		
		System.out.println("Error= " + _nmergeError);
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
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " + 
					_context.countExactNodes(_valueDD) + " nodes, best action: " + 
					_csBestActionInitState);
		}
		
		// Return the best action for the initial state from the last completed trial
		//return best_action_init_state == null ? null : best_action_init_state._string;
	}
	
	// Run a single RTDP trial, return best action as seen from initial state
	public void doRTDPTrial(int trial_depth, ArrayList init_state) throws TimeOutException {
	
		//CString best_action_init_state = null;
		CString best_action = null;
		_sOpen = new Stack<Integer>();
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		Stack<ArrayList> visited_states = new Stack<ArrayList>();
		for (int steps_to_go = _nTrials + 1; steps_to_go > 0/* && !_alGoalStates.contains(cur_state)*/; steps_to_go--) {
			
			//System.out.println("Forward step [" + steps_to_go + "]: " + cur_state);
			
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();

			visited_states.add(cur_state);
			
			// Compute best action for current state (along with Q-value to backup)
			QUpdateResult res = getBestQValue(cur_state);
			if (best_action == null){ // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
			}
			
			// Update Q-value
			_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			_nContUpperUpdates++;
			// Sample next state
			cur_state = sampleNextState(cur_state, res._csBestAction);
		}
		
		if (best_action == null){ // first time through will update
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			QUpdateResult res = getBestQValue(cur_state);
			_csBestActionInitState = res._csBestAction;
			best_action = _csBestActionInitState;
			_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			_nContUpperUpdates++;
		}
		// Do final updates *in reverse* on return
		while(!visited_states.empty()) {

			cur_state = visited_states.pop();
			if (visited_states.size() == 0){
				QUpdateResult res = getBestQValue(cur_state);
				_csBestActionInitState = res._csBestAction;
				_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
				_nContUpperUpdates++;
			}
			if (!LRTDPcheckSolved(cur_state, _nEpsilon)) 
				break;
		}
		_nClosedAdd = _context.getConstantNode(0);
		_nOpenAdd = _context.getConstantNode(0);

		// All of the RTDP updates were just to find out best action from initial state
		// (as a byproduct, we've updated the value function via asychronous DP for
		//  reuse on the next step of this trial and other trials)
		//return best_action_init_state;
	}
	
	public ArrayList <Boolean> ChooseStateAdd(ADDNode node, ArrayList <Boolean> assign, double val){
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				int level_var = (Integer)_context._hmGVarToLevel.get(internalNode._nTestVarID);
				assign.set(level_var, new Boolean(true));
				ArrayList <Boolean> aa = ChooseStateAdd(highNode, assign, val);
				if (aa != null)
					return aa;
				assign.set(level_var, new Boolean(false));
				return ChooseStateAdd(lowNode, assign, val);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				if (probabilidade == val) {					
					ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
					newAssign.addAll(assign);
					return newAssign;
				}
			}			
		}
		return null;
	}
	
	public ArrayList<Boolean> chooseStateOpenStack(){
		int ADD = _sOpen.pop();
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		int num = _context._alOrder.size();
		int vars = num/2;
		for (int i = 0; i <= num; i++)
			assign.add(i<vars? true: null);
		assign = ChooseStateAdd(_context.getNode(ADD), assign, 1d);
		ADD = DDUtils.UpdateValue(_context, ADD, assign, 0d);
		_nOpenAdd = DDUtils.UpdateValue(_context, _nOpenAdd, assign, 0d);
		if (ADD != _context.getConstantNode(0d))
			_sOpen.push(ADD);
		return assign;
	}
	
	private boolean LRTDPcheckSolved(ArrayList cur_state, double epsilon)/*, QUpdateResult res )*/ throws TimeOutException {
		boolean rv = true;		
		_sOpen = new Stack<Integer>();
		_nClosedAdd = _context.getConstantNode(0);
		Stack<ArrayList> closed = new Stack<ArrayList>();
		_nClosed=0;
		_nOpenAdd = _context.getConstantNode(0);		
		if (_context.evaluate(_nSolvedADD, cur_state) == 0.0d){
			_nOpenAdd = DDUtils.UpdateValue(_context, _nOpenAdd, cur_state, 1);
			_sOpen.push(_nOpenAdd);
		}
		while (!_sOpen.isEmpty()) {
			cur_state = chooseStateOpenStack();
			_nClosedAdd = DDUtils.UpdateValue(_context, _nClosedAdd, cur_state, 1);
			closed.push(cur_state);
			_nClosed++;
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			QUpdateResult res = getBestQValue(cur_state);
			//_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			//_nContUpperUpdates++;
			Double residual = Math.abs(_context.evaluate(_valueDD, cur_state)- res._dBestQValue);
			//System.out.println("res = "+residual);
			if (residual == null || residual > epsilon || res._dBestQValue == _dValueRange){
				rv = false;
				continue;
			}
			//System.out.println("pasas o no?");
			CString action = res._csBestAction;			
			Action a = _hmActionName2Action.get(action);			
			int Sucessors = computeSuccesors(cur_state, a._hmVarID2CPT);
			//_context.getGraph(Sucessors).launchViewer();
			reduceRemapLeavesCache = new Hashtable();
			int AB = _context.applyInt(NegativeAdd(_nSolvedADD), Sucessors, DD.ARITH_PROD);
			//_context.getGraph(_nSolvedADD).launchViewer();
			//_context.getGraph(AB).launchViewer();
			reduceRemapLeavesCache = new Hashtable();
			AB = _context.applyInt(AB, NegativeAdd(_nOpenAdd), DD.ARITH_PROD);
			//_context.getGraph(_nOpenAdd).launchViewer();
			//_context.getGraph(AB).launchViewer();
			reduceRemapLeavesCache = new Hashtable();
			AB = _context.applyInt(AB, NegativeAdd(_nClosedAdd), DD.ARITH_PROD);
			//_context.getGraph(_nClosedAdd).launchViewer();
			//_context.getGraph(AB).launchViewer();
			_nOpenAdd = _context.applyInt(_context.applyInt(_nOpenAdd, AB, DD.ARITH_SUM),_context.applyInt(_nOpenAdd, AB, DD.ARITH_PROD), DD.ARITH_MINUS);
			//_context.getGraph(_nOpenAdd).launchViewer();
			if (AB != _context.getConstantNode(0d))
				_sOpen.push(AB);
		}
		if (rv)
			_nSolvedADD = _context.applyInt(_context.applyInt(_nSolvedADD, _nClosedAdd, DD.ARITH_SUM),_context.applyInt(_nSolvedADD, _nClosedAdd, DD.ARITH_PROD), DD.ARITH_MINUS);
		else 
			UpdateVddCS(closed);
		_nClosedAdd = _context.getConstantNode(0d);
		return rv;
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
	public QUpdateResult getBestQValue(ArrayList cur_state) throws TimeOutException {
		
		int prime_vfun = _context.remapGIDsInt(_valueDD, _translation._hmPrimeRemap);

		QUpdateResult result = new QUpdateResult(null, -Double.MAX_VALUE); 
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			Action a = me.getValue();
			double qvalue = getQValue(prime_vfun, cur_state, a._csActionName);
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
	public double getQValue(int prime_vfun, ArrayList cur_state, CString action) throws TimeOutException {
		
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
			checkTimeLimit();
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
			prime_vfun = _context.applyInt(prime_vfun, restricted_cpt_dd, DD.ARITH_PROD);

			///////////////////////////////////////////////////////////////////
			// Sum out next state variable
			///////////////////////////////////////////////////////////////////
			prime_vfun = _context.opOut(prime_vfun, head_var_gid, DD.ARITH_SUM);
		}
		
		if (VERBOSE_LEVEL >= 1) 
			System.out.println("After sum out: " + _context.printNode(prime_vfun));

		// Get action-dependent reward
		double exp_future_val = 
			_context.evaluate(prime_vfun, (ArrayList)null) /* constant - no var assign needed */; 
		double reward = _context.evaluate(a._reward, cur_state);
		
		// Return regressed value for current state
		return reward + _dDiscount * exp_future_val;
	}
	
	public void UpdateVdd(int closed) throws TimeOutException {
		_nMaskedE = closed;
		_nE = _context.applyInt(_valueDD, closed, DD.ARITH_PROD);
		UpdateAbstractState();
		reduceRemapLeavesCache = new Hashtable();
		_nMaskedE = reduceRemapLeaves(_nE);
		reduceRemapLeavesCache = new Hashtable();
		int maskedNE = NegativeAdd(_nMaskedE);
		int NE = _context.applyInt(_valueDD, maskedNE, DD.ARITH_PROD);
		_valueDD = _context.applyInt(_nE, NE, DD.ARITH_SUM);
		//System.out.println("spudd update " + _nClosed);
		_nContUpperUpdates+= _nClosed;
	}
	
	public void UpdateVddCS(Stack<ArrayList> closed) throws TimeOutException {
		ArrayList<Boolean> assign;
		while(!closed.isEmpty()){
			assign = closed.pop();
			QUpdateResult res = getBestQValue(assign);
			_valueDD = DDUtils.UpdateValue(_context, _valueDD, assign, res._dBestQValue);
			_nContUpperUpdates++;
		}
	}
	public void UpdateVddCS1() throws TimeOutException {
		ArrayList<Boolean> assign;
		int num = _context._alOrder.size();
		int vars = num/2;
		while(_nClosedAdd != _context.getConstantNode(0d)){
			assign = new ArrayList<Boolean>();
			for (int i = 0; i <= num; i++)
				assign.add(i<vars? false: null);
			assign = ChooseStateAdd(_context.getNode(_nClosedAdd), assign, 1d);
			QUpdateResult res = getBestQValue(assign);
			_valueDD = DDUtils.UpdateValue(_context, _valueDD, assign, res._dBestQValue);
			_nContUpperUpdates++;
			_nClosedAdd = DDUtils.UpdateValue(_context, _nClosedAdd, assign, 0d);
		}
	}

	public void UpdateAbstractState() throws TimeOutException {
		// Cache maintenance
		flushCaches();			
		// Prime the value function
		_nE = _context.remapGIDsInt(_nE, _translation._hmPrimeRemap);
		// Cache maintenance -- clear out previous nodes, but save Q-functions
		clearSaveNodes();
		//////////////////////////////////////////////////////////////
		// Iterate over each action to obtain Q-function from _valueDD
		//////////////////////////////////////////////////////////////
		_nmaxDD = -1;
		HashMap<CString,Integer> temp_regr = new HashMap<CString,Integer>();
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			CString action_name = me.getKey();
			Action a = me.getValue();
			// Regress the current value function through each action
			int regr = regress(_nE, a, true);
			saveNode(regr); // Save latest Q-function regression
			flushCaches();
			checkTimeLimit();
			// Take the max over this action and the previous action
			_nmaxDD = (_nmaxDD == -1? regr: _context.applyInt(_nmaxDD, regr, DD.ARITH_MAX));
			// Cache maintenance - after maximization
			flushCaches();
			checkTimeLimit();
		}
		_nE = _nmaxDD;		
	}
	
	public int regress(int vfun, Action a, boolean flush_caches) throws TimeOutException {
		int dd_ret = vfun;
		// Find what gids (ADD level assignments of variables) are currently in vfun
		Set vfun_gids = _context.getGIDs(vfun);
		//////////////////////////////////////////////////////////////
		// For each next-state variable in DBN for action 'a'
		//////////////////////////////////////////////////////////////
		for (Map.Entry<Integer, Integer> me : a._hmVarID2CPT.entrySet()) {
			Integer cpt_dd  = me.getValue();
			Integer head_var_gid = me.getKey();
			// No need to regress variables not in the value function  
			if (!vfun_gids.contains(head_var_gid))
				continue;
			///////////////////////////////////////////////////////////////////
			// Multiply next state variable DBN into current value function
			///////////////////////////////////////////////////////////////////
			clearSaveNode(dd_ret);
			dd_ret = _context.applyInt(dd_ret, cpt_dd, DD.ARITH_PROD);
			saveNode(dd_ret);
			flushCaches();
			checkTimeLimit();
			///////////////////////////////////////////////////////////////////
			// Sum out next state variable
			///////////////////////////////////////////////////////////////////
			clearSaveNode(dd_ret);
			dd_ret = _context.opOut(dd_ret, head_var_gid, DD.ARITH_SUM);
			saveNode(dd_ret);
			flushCaches();
			checkTimeLimit();
		}
		// Discount the regressed function (if needed)
		if (_dDiscount < 1d)
			dd_ret = _context.scalarMultiply(dd_ret, _dDiscount);
		// Add in action-dependent reward
		//int rewardrestrictectE = _context.applyInt(a._reward, _nMaskedE, DD.ARITH_PROD);
		dd_ret = _context.applyInt(dd_ret, a._reward/*rewardrestrictectE*/, DD.ARITH_SUM);
		// Return regressed value function
		return dd_ret;
	}
	
    private int reduceRemapLeaves(int id) {
		
		Integer Fr= (Integer)reduceRemapLeavesCache.get(id);
    	if(Fr==null){
    		ADDNode nodeKey=_context.getNode(id);
    		if(nodeKey instanceof ADDINode){
	    		Integer Fh=reduceRemapLeaves(((ADDINode)nodeKey)._nHigh);
	    		Integer Fl=reduceRemapLeaves(((ADDINode)nodeKey)._nLow);
	    		Integer Fvar= ((ADDINode)nodeKey)._nTestVarID;
	    		Fr=_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	}
    		else{
    			ADDDNode nod = (ADDDNode)nodeKey;
    			return _context.getConstantNode(nod._dUpper>0d?1d:0d);
    		}
    	}
    	return Fr;
	}
    private int NegativeAdd(int id) {
		
		Integer Fr= (Integer)reduceRemapLeavesCache.get(id);
    	if(Fr==null){
    		ADDNode nodeKey=_context.getNode(id);
    		if(nodeKey instanceof ADDINode){
	    		Integer Fh=NegativeAdd(((ADDINode)nodeKey)._nHigh);
	    		Integer Fl=NegativeAdd(((ADDINode)nodeKey)._nLow);
	    		Integer Fvar= ((ADDINode)nodeKey)._nTestVarID;
	    		Fr=_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	}
    		else{
    			ADDDNode nod = (ADDDNode)nodeKey;
    			return _context.getConstantNode(nod._dUpper>0?0d:1d);
    		}
    	}
    	return Fr;
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

	// Clear nodes on save list
	public void clearSaveNodes() {
		_alSaveNodes.clear();
	}
	
	// Remove nodes on save list
	public void clearSaveNode(Integer dd) {
		_alSaveNodes.remove(dd);
	}

	// Add node to save list
	public void saveNode(Integer dd) {
		_alSaveNodes.add(dd);
	}
	
	// Frees up memory... only do this if near limit?
	public void flushCaches() {
		if (!ALWAYS_FLUSH
				&& ((double) RUNTIME.freeMemory() / (double) RUNTIME
						.totalMemory()) > FLUSH_PERCENT_MINIMUM) {
			return; // Still enough free mem to exceed minimum requirements
		}

		_context.clearSpecialNodes();
		for (Integer dd : _alSaveNodes)
			_context.addSpecialNode(dd);
		for (Integer dd : _allMDPADDs)
			_context.addSpecialNode(dd);
		for (Integer dd : _sOpen)
			_context.addSpecialNode(dd);
		_context.addSpecialNode(_nE);
		_context.addSpecialNode(_nmaxDD);
		_context.addSpecialNode(_nMaskedE);
		_context.addSpecialNode(_valueDD);
		_context.addSpecialNode(_nClosedAdd);
		_context.addSpecialNode(_nOpenAdd);
		_context.addSpecialNode(_nSolvedADD);

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
	
	private int computeSuccesors(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
		Integer multCPTs=_context.getConstantNode(1d);
		Integer xiprime, xi;
		for (CString x : _alStateVars){		
			xiprime=(Integer)_context._hmVarName2ID.get(_translation._hmPrimeRemap.get(x._string));
			xi =(Integer)_context._hmVarName2ID.get(x._string);
			Integer cpt_a_xiprime = iD2ADD.get(xiprime);
			double probTrue,probFalse;
			int levelprime = (Integer)_context._hmGVarToLevel.get(xiprime);
			state.set(levelprime, true);
			probTrue=_context.evaluate(cpt_a_xiprime,state);
			state.set(levelprime, null);			
			if (probTrue == 0d || probTrue == 1d){
				probFalse = 1 - probTrue;
				Integer Fh=_context.getConstantNode(probTrue);
				Integer Fl=_context.getConstantNode(probFalse);			
				Integer newCPT = _context.getINode(xi, Fl, Fh, true);
				multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
			}
		}
		return multCPTs;
	}
	
	public void inOrderSearch (ADDNode node, ArrayList <Boolean> assign, ArrayList<ArrayList> alEstadoProb){
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
				assign.set(level_var, null);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de serem alcançados
				if (probabilidade > 0.0d) {					
					AddStates(assign, 0, alEstadoProb);
				}
			}
		}
	}
	
	public void AddStates(ArrayList s, int ind, ArrayList<ArrayList> alEstadoProb){
		if (_alStateVars.size() ==ind){
			ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
			newAssign.addAll(s);
			alEstadoProb.add(newAssign);
		}
		else
			if (s.get(ind) == null){
				s.set(ind, new Boolean(true));
				AddStates(s, ind+1, alEstadoProb);
				s.set(ind, new Boolean(false));
				AddStates(s, ind+1, alEstadoProb);
				s.set(ind, null);
			}
			else
				AddStates(s, ind+1, alEstadoProb);
	}
	
	
	public HashSet reduceInternal;
	public Integer pruneNodesValue(int id, double mergeError) {        
        reduceRemapLeavesCache=new Hashtable();
        reduceInternal=new HashSet();
		ArrayList hsLeaves = new ArrayList();
		collectLeavesADD(id, hsLeaves);
		HashMap finalMap = compressLeaves(hsLeaves, mergeError);
		return reduceRemapLeaves(id, finalMap);
	}

	public void collectLeavesADD(int id, ArrayList hsLeaves) {
		ADDNode node=_context.getNode(id);
		if(node instanceof ADDDNode){
			if (!hsLeaves.contains(new PrunningNode(id, ((ADDDNode) node)._dLower)))
				hsLeaves.add(new PrunningNode(id, ((ADDDNode) node)._dLower));
		} 
		else {//internal node
			if(!reduceInternal.contains(id)){
				ADDINode nodeInternal = (ADDINode) node;
				collectLeavesADD(nodeInternal._nHigh, hsLeaves);
				collectLeavesADD(nodeInternal._nLow, hsLeaves);
				reduceInternal.add(id);
			}
		}
	}
	
	public HashMap compressLeaves(ArrayList hsLeaves, double mergeError) {
		Collections.sort(hsLeaves);
		HashMap<Integer, Integer> hmNodes = new HashMap<Integer, Integer>();
		ADDDNode nodo = null;
		int idnodo = -1;
		double soma =0;
		double max = Double.NEGATIVE_INFINITY;
		int numElem = 0;
		for (int i=0;i<hsLeaves.size();i++){
			PrunningNode nodoprun =(PrunningNode)hsLeaves.get(i);
			if (nodoprun._dValue <= max){				 
				soma += nodoprun._dValue;
				numElem++;				
			}
			else{
				if (nodo != null)
					nodo._dUpper = nodo._dLower = soma/numElem;
				idnodo = nodoprun._nid;
				nodo = (ADDDNode)_context.getNode(idnodo);
				max = nodoprun._dValue + mergeError;//((nodoprun._dValue < 0 ? -1 : 1) * mergeError);
				soma = nodoprun._dValue;
				numElem = 1;
			}
			hmNodes.put(nodoprun._nid, idnodo);
		}
		return hmNodes;
	}
	
	private int reduceRemapLeaves(int id, HashMap finalMap) {
		
		Integer Fr= (Integer)reduceRemapLeavesCache.get(id);
    	if(Fr==null){
    		ADDNode nodeKey=_context.getNode(id);
    		if(nodeKey instanceof ADDINode){
	    		Integer Fh=reduceRemapLeaves(((ADDINode)nodeKey)._nHigh,finalMap);
	    		Integer Fl=reduceRemapLeaves(((ADDINode)nodeKey)._nLow,finalMap);
	    		Integer Fvar= ((ADDINode)nodeKey)._nTestVarID;
	    		Fr=_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	}
    		else// find terminal node in the finalMap
    			return (Integer)finalMap.get(id);
    	}
    	return Fr;
	}

	public class PrunningNode implements Comparable { 

		private int _nid; 
		private Double _dValue; 

		public PrunningNode(int id, double value) {
			_nid = id; 
			_dValue = value;
		} 

		public String toString(){
			return ("ID: " + _nid + " Value: " + _dValue);
		} 

		public String getNombre() {
			return _dValue.toString();
		} 

		public boolean equals( Object node ) {			 
			return (node!= null && node instanceof PrunningNode && ((PrunningNode)node)._nid == _nid && ((PrunningNode)node)._dValue.equals(_dValue));
		} 

		public int hashCode() { 
			return this._dValue.hashCode();
		} 

		public int compareTo( Object node ) {
			if (node instanceof PrunningNode){
				PrunningNode Pnode = (PrunningNode)node; 
				return(_dValue.compareTo(Pnode._dValue));
			}
			else return -1;
		}
	}
	
	/*public void MaxState(int id, ArrayList state){
		ADDNode node = _context.getNode(id);
		if (node instanceof ADDINode) {			
			Boolean LH = _context.getMaxValue(((ADDINode)node)._nHigh)>_context.getMaxValue(((ADDINode)node)._nLow);
			Boolean LHeq = _context.getMaxValue(((ADDINode)node)._nHigh)==_context.getMaxValue(((ADDINode)node)._nLow);
			int proxid = LH?((ADDINode)node)._nHigh: ((ADDINode)node)._nLow;
			int proxideq = !LH?((ADDINode)node)._nHigh: ((ADDINode)node)._nLow;
			int level_var = (Integer)_context._hmGVarToLevel.get(((ADDINode)node)._nTestVarID);
			state.set(level_var, LH);
			MaxState(proxid, state);
			if (LHeq){
				state.set(level_var, !LH);
				MaxState(proxideq, state);
			}
		}
		else{
			ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
			newAssign.addAll(state);
			if (!_alGoalStates.contains(state)){
				_alGoalStates.add(newAssign);
				//_lSolvedStates.add(newAssign);
			}
		}
	}*/
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
