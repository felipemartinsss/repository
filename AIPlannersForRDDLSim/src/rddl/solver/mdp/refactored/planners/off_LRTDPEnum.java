package rddl.solver.mdp.refactored.planners;

import java.io.IOException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Random;
import java.util.Stack;
import java.util.TreeSet;

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
import util.Cronometro;
import util.Pair;
import util.ProbState;
import util.QUpdateResult;
import util.StochasticBisimulationCommons;
import dd.discrete.ADD;
import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;

/**
 * 
 * @author Felipe Martins and Mijail Gamarra Holguin
 *
 */
public class off_LRTDPEnum extends Policy {

	private static double SOLVER_TIME_LIMIT_PER_TURN = 2d; // Solver time limit
															// (seconds)

	private final static boolean SHOW_STATE = true;
	private final static boolean SHOW_ACTIONS = true;
	private final static boolean SHOW_ACTION_TAKEN = true;

	// Only for diagnostics, comment this out when evaluating
	private final static boolean DISPLAY_SPUDD_ADDS_GRAPHVIZ = false;
	private final static boolean DISPLAY_SPUDD_ADDS_TEXT = false;
	private static final String LOG_FILE = "rddloffline";

	private RDDL2Format _translation = null;

	// Using CString wrapper to speedup hash lookups
	private ADD _context;
	private ArrayList<Integer> _allMDPADDs;
	private ArrayList<CString> _alStateVars;
	private ArrayList<CString> _alPrimeStateVars;
	private ArrayList<CString> _alActionNames;
	private int _nContUpperUpdates; // For computing the number of value
									// function updates
	private HashMap<CString, Action> _hmActionName2Action; // Holds transition
															// function
	private ArrayList<ArrayList> _lSolvedStates = new ArrayList<ArrayList>();

	// State variables
	private int _nRemainingHorizon = -1;

	// Just use the default random seed
	private Random _rand = new Random();
	private int _nProf = 5;
	private int _nGetActions = 0;
	private int _nRound = 0;
	private double base = 1.04648d;

	private Cronometro lrtdpTime;

	private Object initialState;

	// Local constants
	private final static int VERBOSE_LEVEL = 0; // Determines how much output is
												// displayed

	private final static boolean ALWAYS_FLUSH = false; // Always flush DD
														// caches?
	private final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush
																// until < this
																// amt

	// For printing
	private final static DecimalFormat _df = new DecimalFormat("#.###");

	// Timing variables
	private long _lStartTime; // For timing purposes
	private double _nTimeLimitSecs;
	private static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	private INSTANCE _rddlInstance = null;
	private HashMap<ArrayList<Boolean>, Double> _valueDD;
	private int _nDDType; // Type of DD to use
	private int _nTrials;
	private double _dRewardRange; // Important if approximating
	private double _dValueRange; // Important if approximating
	private double _dDiscount;
	private int _nHorizon;
	private CString _csBestActionInitState = null;
	private HashMap<Integer, Integer> _hmPrimeVarID2VarID;
	private HashMap<ArrayList, HashMap<CString, Double>> _hmReward;
	private boolean WRITE_TO_LOG = false;
	private HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>> _hmStateTransition = new HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>>();
	private double initialStateValue;
	
	// Constructors
	public off_LRTDPEnum() {
	}

	public off_LRTDPEnum(String instance_name) {
		super(instance_name);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// /////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		// _nGetActions++;
		// _nProf = _nGetActions<=13?7:_nGetActions<=26?5:3;
		SOLVER_TIME_LIMIT_PER_TURN = Math.pow(base,
				base >= 1 ? _nRemainingHorizon : _nHorizon - _nRemainingHorizon
						+ 1) / 3;
		// System.out.println("FULL STATE:\n\n" +
		// SPerseusSPUDDPolicy.getStateDescription(s));

		if (s == null) {
			// This should only occur on the **first step** of a POMDP trial
			System.err.println("ERROR: NO STATE/OBS: MDP must have state.");
			System.exit(1);
		}

		// Get a set of all true observation or state variables
		TreeSet<CString> true_vars = CString
				.Convert2CString(SPerseusSPUDDPolicy
						.getTrueFluents(s, "states"));
		if (SHOW_STATE) {
			System.out
					.println("\n==============================================");
			System.out.println("\nTrue state variables:");
			for (CString prop_var : true_vars)
				System.out.println(" - " + prop_var);
		}

		// Get a map of { legal action names -> RDDL action definition }
		Map<String, ArrayList<PVAR_INST_DEF>> action_map = ActionGenerator
				.getLegalBoolActionMap(s);

		// RTDP algorithm
		//
		// Everytime we reach a state, do a number of trials starting from this
		// state and going to end of horizon. At each step of trial, compute
		// local backups and in the process the best action (especially
		// keep track of for starting state). Use trick to evaluate then
		// correct ADD for ADD value update.

		// Use the precomputed q-functions (cached when the value function
		// was computed) to determine the best action for this state
		ArrayList add_state_assign = DDUtils.ConvertTrueVars2DDAssign(_context,
				true_vars, _alStateVars);
		_csBestActionInitState = null;
		if (_nGetActions == 0) {
			lrtdpTime = new Cronometro();
			lrtdpTime.setStart();
			initialState = add_state_assign.clone();
			doRTDP(SOLVER_TIME_LIMIT_PER_TURN, add_state_assign);
			lrtdpTime.setEnd();
			
			// Remove the call below if you want to  see the results of Simulator class.
			System.exit(0);
		}
		_nGetActions++;

		QUpdateResult resultQ = null;
		try {
			resultQ = getBestQValue(add_state_assign);
			_csBestActionInitState = resultQ._csBestAction;
		} catch (TimeOutException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		String action_taken = (_csBestActionInitState == null ? null
				: _csBestActionInitState._string);
		if (action_taken == null) {
			// No RTDP results available, just take random action
			ArrayList<String> actions = new ArrayList<String>(
					action_map.keySet());
			action_taken = actions.get(_rand.nextInt(actions.size()));
			if (SHOW_ACTION_TAKEN)
				System.out.println("\n--> [Random] action taken: "
						+ action_taken);
		} else if (SHOW_ACTION_TAKEN)
			// System.out.println("Current state: " + add_state_assign);
			System.out.println("\n--> [RTDP] best action taken: "
					+ action_taken);
		// System.out.println("Number of VUpper Updates: "+_nContUpperUpdates);
		--_nRemainingHorizon; // One less action to take
		return action_map.get(action_taken);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Round / Session Signals
	//
	// If you need to keep track of state information across rounds or sessions,
	// just modify these methods. (Each session consists of total_rounds
	// rounds.)
	// /////////////////////////////////////////////////////////////////////////

	public void roundInit(double time_left, int horizon, int round_number,
			int total_rounds) {
		super.roundInit(time_left, horizon, round_number, total_rounds);

		// Reset horizon
		_nRemainingHorizon = horizon;
		_nGetActions = 0;
		_nRound++;
		SOLVER_TIME_LIMIT_PER_TURN = _nRound <= 10 ? 2d : _nRound <= 20 ? 1.5d
				: 1d;
		// Build ADDs for transition, reward and value function (if not already
		// built)
		if (_translation == null) {

			// Use RDDL2Format to build SPUDD ADD translation of _sInstanceName
			try {
				_translation = new RDDL2Format(_rddl, _sInstanceName,
						RDDL2Format.SPUDD_CURR, "");
			} catch (Exception e) {
				System.err.println("Could not construct MDP for: "
						+ _sInstanceName + "\n" + e);
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
			_hmActionName2Action = new HashMap<CString, Action>();
			for (String a : _translation._hmActionMap.keySet()) {
				HashMap<CString, Integer> cpts = new HashMap<CString, Integer>();
				int reward = _context.getConstantNode(0d);

				// Build reward from additive decomposition
				ArrayList<Integer> reward_summands = _translation._act2rewardDD
						.get(a);
				for (int summand : reward_summands)
					reward = _context.applyInt(reward, summand, ADD.ARITH_SUM);
				_allMDPADDs.add(reward);

				// Build CPTs
				for (String s : _translation._alStateVars) {
					int dd = _translation._var2transDD.get(new Pair(a, s));

					int dd_true = _context.getVarNode(s + "'", 0d, 1d);
					dd_true = _context.applyInt(dd_true, dd, ADD.ARITH_PROD);

					int dd_false = _context.getVarNode(s + "'", 1d, 0d);
					// System.out.println("Multiplying..." + dd + ", " +
					// DD_ONE);
					// _context.printNode(dd);
					// _context.printNode(DD_ONE);
					int one_minus_dd = _context.applyInt(
							_context.getConstantNode(1d), dd, ADD.ARITH_MINUS);
					dd_false = _context.applyInt(dd_false, one_minus_dd,
							ADD.ARITH_PROD);

					// Now have "dual action diagram" cpt DD
					int cpt = _context.applyInt(dd_true, dd_false,
							ADD.ARITH_SUM);

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
					System.out.println("Content of action '" + a + "'\n"
							+ action);
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
						_context.getGraph(action._hmStateVar2CPT.get(var))
								.launchViewer();

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

	/**
	 * Prints the final reward. 
	 */
	public void roundEnd(double reward) {
		new StochasticBisimulationCommons().timeInfo("LRTDPTime", _sInstanceName, initialStateValue, lrtdpTime, reward);
		System.out
				.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out
				.println("*********************************************************");

		// _context.getGraph(_valueDD).launchViewer(1300, 770);
	}

	/**
	 * Initialize all variables (call before starting value iteration)
	 */
	public void resetSolver() {
		_nTrials = -1;
		_rddlInstance = _rddl._tmInstanceNodes.get(this._sInstanceName);
		if (_rddlInstance == null) {
			System.err.println("ERROR: Could not fine RDDL instance '"
					+ _rddlInstance + "'");
			System.exit(1);
		}
		_dDiscount = _rddlInstance._dDiscount;
		if (_dDiscount == 1d)
			_dDiscount = 0.99d;
		_nHorizon = _rddlInstance._nHorizon;

		// In RTDP we need to map from CPT head var (primed) into non-prime
		// state variable
		_hmPrimeVarID2VarID = new HashMap<Integer, Integer>();
		for (Map.Entry<String, String> me : _translation._hmPrimeRemap
				.entrySet()) {
			String var = me.getKey();
			String var_prime = me.getValue();
			Integer var_id = (Integer) _context._hmVarName2ID.get(var);
			Integer var_prime_id = (Integer) _context._hmVarName2ID
					.get(var_prime);
			if (var_id == null || var_prime_id == null) {
				System.err.println("ERROR: Could not get var IDs " + var_id
						+ "/" + var_prime_id + " for " + var + "/" + var_prime);
				System.exit(1);
			}
			_hmPrimeVarID2VarID.put(var_prime_id, var_id);
		}
		_hmReward = new HashMap<ArrayList, HashMap<CString, Double>>();
		_dRewardRange = -Double.MAX_VALUE;
		/*
		 * for (Action a : _hmActionName2Action.values()) _dRewardRange =
		 * Math.max(_dRewardRange, _context.getMaxValue(a._reward) -
		 * _context.getMinValue(a._reward));
		 */
		for (Action a : _hmActionName2Action.values())
			_dRewardRange = Math.max(_dRewardRange,
					_context.getMaxValue(a._reward));
		double value_range = (_dDiscount < 1d) ? _dRewardRange
				/ (1d - _dDiscount) // being lazy: assume infinite horizon
		: _nHorizon * _dRewardRange; // assume max reward over horizon
		_dValueRange = value_range;
		// System.out.println("Heuristica admissivel: " + _dValueRange);
		// System.exit(0);
		// IMPORTANT: RTDP needs **optimistic upper bound initialization**
		/*
		 * double value_range = (_dDiscount < 1d) ? _dRewardRange / (1d -
		 * _dDiscount) // being lazy: assume infinite horizon : _nHorizon *
		 * _dRewardRange; // assume max reward over horizon
		 */
		// _valueDD = _context.getConstantNode(value_range);
		_valueDD = new HashMap<ArrayList<Boolean>, Double>();
		// base = timeInstance();
	}

	/**
	 * Main RTDP Algorithm
	 * @param time_limit_secs
	 * @param init_state
	 */
	public void doRTDP(double time_limit_secs, ArrayList init_state) {

		// System.out.println("RTDP: Time limit: " + _nTimeLimitSecs +
		// " seconds, discount: " + _dDiscount + ", horizon: " +
		// _nRemainingHorizon + "/" + _nHorizon);

		_nTimeLimitSecs = time_limit_secs;
		_lStartTime = System.currentTimeMillis();
		// CString best_action_init_state = null;
		try {
			// Trial depth should be exactly equal to remaining horizon-to-go on
			// this round
			// writeToLog(_sInstanceName);
			_nTrials = 0;
			while (!_lSolvedStates.contains(init_state)) {
				doRTDPTrial(_nRemainingHorizon, init_state);
				_nTrials++;
			}
			
			initialStateValue = _valueDD.get(init_state);
			// writeToLog("Fin");
			// System.exit(1);
		} catch (TimeOutException e) {
			System.out.println("RTDP: TIME LIMIT EXCEEDED after " + _nTrials
					+ " trials.");
		} catch (Exception e) {
			System.err.println("RTDP: ERROR at " + _nTrials + " trials.");
			e.printStackTrace(System.err);
			System.exit(1);
		} finally {
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " /*
																		 * + /*
																		 * _context
																		 * .
																		 * countExactNodes
																		 * (
																		 * _valueDD
																		 * ) +
																		 * " nodes, best action: "
																		 * +
																		 * _csBestActionInitState
																		 */);
		}

		// Return the best action for the initial state from the last completed
		// trial
		// return best_action_init_state == null ? null :
		// best_action_init_state._string;
	}

	/**
	 * Run a single RTDP trial, return best action as seen from initial state
	 * @param trial_depth
	 * @param init_state
	 * @throws TimeOutException
	 * @throws IOException
	 */
	public void doRTDPTrial(int trial_depth, ArrayList init_state)
			throws TimeOutException, IOException {

		// CString best_action_init_state = null;
		CString best_action = null;
		// //////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way),
		// then
		// backtrack and update in reverse.
		// //////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>();
		Date seed = new Date();
		Random rand = new Random(seed.getTime());
		double randomTerminateValue;

		while (!_lSolvedStates.contains(cur_state)) {
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			// checkTimeLimit();
			visited_states.add(cur_state);
			// Compute best action for current state (along with Q-value to
			// backup)
			QUpdateResult res = getBestQValue(cur_state);
			if (best_action == null) { // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
			}

			_valueDD.put(cur_state, res._dBestQValue);
			_nContUpperUpdates++;
			// Sample next state
			randomTerminateValue = rand.nextDouble();
			if (randomTerminateValue > _dDiscount) {
				break;
			} else {
				cur_state = SortearEstado(res._alProbEstados);
			}
		}

		for (int depth = visited_states.size() - 1; depth >= 0; depth--) {

			cur_state = visited_states.get(depth);
			if (visited_states.size() == 0) {
				QUpdateResult res = getBestQValue(cur_state);
				_csBestActionInitState = res._csBestAction;
				// if(_valueDD.containsKey(cur_state))
				// _valueDD.remove(cur_state);
				_valueDD.put(cur_state, res._dBestQValue);
				_nContUpperUpdates++;
				// double instant = (System.currentTimeMillis() - _lStartTime) /
				// 1000d;
				// writeToLog(instant+ "	"+res._dBestQValue);
			}
			if (!LRTDPcheckSolved(cur_state, 0.001, visited_states.size() - 1))
				break;
		}

		// All of the RTDP updates were just to find out best action from
		// initial state
		// (as a byproduct, we've updated the value function via asychronous DP
		// for
		// reuse on the next step of this trial and other trials)
		// return best_action_init_state;
	}

	/**
	 * Run the checkSolved part of LRTDP.
	 * @param cur_state
	 * @param epsilon
	 * @param depth
	 * @return
	 * @throws TimeOutException
	 */
	public boolean LRTDPcheckSolved(ArrayList cur_state, double epsilon,
			int depth)/* , QUpdateResult res ) */throws TimeOutException {
		boolean rv = true;
		Stack<ArrayList> open = new Stack<ArrayList>();
		Stack<ArrayList> closed = new Stack<ArrayList>();
		ArrayList<ArrayList> aux = new ArrayList<ArrayList>();
		if (!_lSolvedStates.contains(cur_state)) {
			open.push(cur_state);
			aux.add(cur_state);
		}
		while (!open.isEmpty()) {
			cur_state = open.pop();
			closed.push(cur_state);
			aux.add(cur_state);
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			// checkTimeLimit();
			QUpdateResult res = getBestQValue(cur_state);
			Double residual = Math.abs(_valueDD.get(cur_state)
					- res._dBestQValue);
			if (residual == null || residual > epsilon) {
				rv = false;
				continue;
			}
			CString action = res._csBestAction;
			Action a = _hmActionName2Action.get(action);
			ArrayList<ProbState> lSucessors = computeSuccesorsProbEnum(
					cur_state, a._hmVarID2CPT);
			Iterator it = lSucessors.listIterator();
			while (it.hasNext()) {
				flushCaches(); // Only thing to keep is MDP def. and current
								// vfun
				// checkTimeLimit();
				ProbState s_prime = (ProbState) it.next();
				if (s_prime._dProb != 0d
						&& !_lSolvedStates.contains(s_prime.nextRepresentant)
						&& !aux.contains(s_prime.nextRepresentant)) {
					open.push(s_prime.nextRepresentant);
					aux.add(s_prime.nextRepresentant);
				}
			}
		}
		if (rv)
			for (ArrayList state : closed) {
				_lSolvedStates.add(state);
			}
		else
			while (!closed.isEmpty()) {
				flushCaches();
				// checkTimeLimit();
				cur_state = closed.pop();
				QUpdateResult resultQ = getBestQValue(cur_state);
				if (_valueDD.containsKey(cur_state))
					_valueDD.remove(cur_state);
				_valueDD.put(cur_state, resultQ._dBestQValue);
				_nContUpperUpdates++;
			}
		return rv;
	}

	/**
	 * Find best Q-value/action for given state
	 * @param cur_state
	 * @return
	 * @throws TimeOutException
	 */
	public QUpdateResult getBestQValue(ArrayList cur_state)
			throws TimeOutException {
		QUpdateResult result = new QUpdateResult(null, -Double.MAX_VALUE,
				new ArrayList<ProbState>());
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			Action a = me.getValue();
			Pair<Double, ArrayList<ProbState>> qvalue = getQValue(cur_state,
					a._csActionName);
			if (result._csBestAction == null
					|| qvalue._o1 > result._dBestQValue) {
				result._csBestAction = a._csActionName;
				result._dBestQValue = qvalue._o1;
				result._alProbEstados = qvalue._o2;
			}
			// System.out.println("- " +a._csActionName + "(" + qvalue + ")");
		}
		// System.out.println("=> " + result._csBestAction + "(" +
		// result._dBestQValue + ")");
		return result;
	}

	/**
	 * Find Q-value for action in given state
	 * @param cur_state
	 * @param action
	 * @return
	 * @throws TimeOutException
	 */
	public Pair<Double, ArrayList<ProbState>> getQValue(ArrayList cur_state,
			CString action) throws TimeOutException {

		Action a = _hmActionName2Action.get(action);
		// keys = new HashMap<ArrayList<Boolean>, Integer>();
		Pair stateAction = new Pair(cur_state, a);
		ArrayList<ProbState> ProbsStates = _hmStateTransition.get(stateAction);
		if (ProbsStates == null) {
			ProbsStates = computeSuccesorsProbEnum(cur_state, a._hmVarID2CPT);
			_hmStateTransition.put(stateAction, ProbsStates);
		}

		// ////////////////////////////////////////////////////////////
		// For each next-state in DBN for action 'a'
		// ////////////////////////////////////////////////////////////
		double soma = 0;
		for (int indice = 0; indice < ProbsStates.size() - 1; indice++) {
			// checkTimeLimit();
			ProbState pS = ProbsStates.get(indice);
			if (!_valueDD.containsKey(pS.nextRepresentant))
				_valueDD.put(pS.nextRepresentant, _dValueRange);
			double valor = _valueDD.get(pS.nextRepresentant);
			double prob = pS._dProb - ProbsStates.get(indice + 1)._dProb;
			soma += (prob * valor);
		}
		// Get action-dependent reward
		double reward = 0;
		if (_hmReward.containsKey(cur_state)
				&& _hmReward.get(cur_state).containsKey(action))
			reward = _hmReward.get(cur_state).get(action);
		else
			reward = _context.evaluate(a._reward, cur_state);
		// Return regressed value for current state
		return new Pair<Double, ArrayList<ProbState>>(reward + _dDiscount
				* soma, ProbsStates);
	}

	/**
	 * Compute one step sucessors given a current state.
	 * @param state
	 * @param iD2ADD
	 * @return
	 */
	private ArrayList<ProbState> computeSuccesorsProbEnum(ArrayList state,
			HashMap<Integer, Integer> iD2ADD) {
		Integer multCPTs = _context.getConstantNode(1d);
		Integer xiprime;
		for (CString x : _alStateVars) {
			xiprime = (Integer) _context._hmVarName2ID
					.get(_translation._hmPrimeRemap.get(x._string));
			Integer cpt_a_xiprime = iD2ADD.get(xiprime);
			double probTrue, probFalse;
			int levelprime = (Integer) _context._hmGVarToLevel.get(xiprime);
			state.set(levelprime, true);
			probTrue = _context.evaluate(cpt_a_xiprime, state);
			state.set(levelprime, null);
			probFalse = 1 - probTrue;
			Integer Fh = _context.getConstantNode(probTrue);
			Integer Fl = _context.getConstantNode(probFalse);
			Integer newCPT = _context.getINode(xiprime, Fl, Fh, true);
			multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
		}
		ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		for (int i = 0; i <= _context._alOrder.size(); i++)
			assign.add(null);
		inOrderSearch(_context.getNode(multCPTs), assign, alEstadoProb);
		alEstadoProb.get(0)._dProb = 1;
		alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		return alEstadoProb;
	}

	/*
	 * Perform a InOrder search (left-root-right) in the trees and adds a pair
	 * (state, probability) in a HashMap when reaches a leaf in the tree.
	 * @param node
	 * 
	 * @param s
	 * 
	 * @param alEstadoProb
	 */
	public void inOrderSearch(ADDNode node, ArrayList<Boolean> assign,
			ArrayList<ProbState> alEstadoProb) {
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				int id_var_prime = _hmPrimeVarID2VarID
						.get(internalNode._nTestVarID);
				int level_var = (Integer) _context._hmGVarToLevel
						.get(id_var_prime);
				assign.set(level_var, new Boolean(false));
				// Expande a subárvore low
				inOrderSearch(lowNode, assign, alEstadoProb);
				assign.set(level_var, new Boolean(true));
				// Expande a subárvore high
				inOrderSearch(highNode, assign, alEstadoProb);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de
				// serem alcançados
				if (probabilidade > 0.0d) {
					Double probanterior = (alEstadoProb.isEmpty() ? 0.0d
							: alEstadoProb.get(0)._dProb);
					ArrayList<Boolean> newAssign = new ArrayList<Boolean>();
					newAssign.addAll(assign);
					ProbState novoNo = new ProbState(probanterior
							+ probabilidade, newAssign);
					alEstadoProb.add(0, novoNo);
				}
			}
		}
	}

	/**
	 * Sample the next state to be visited by LRTDP.
	 * @param alEstadoProb
	 * @return
	 */
	public ArrayList<Boolean> SortearEstado(ArrayList<ProbState> alEstadoProb) {
		int inicio = 0;
		int fin = alEstadoProb.size() - 2;
		int mitade = (fin + inicio) / 2;
		Random alNumber = new Random();
		double rand = alNumber.nextDouble();
		ProbState upper = alEstadoProb.get(mitade);
		ProbState lower = alEstadoProb.get(mitade + 1);
		int indice = 0;
		while ((rand > upper._dProb || rand <= lower._dProb)
				&& fin - inicio > 1) {
			if (indice > 15)
				System.out.println(indice);
			if (rand > upper._dProb)
				fin = mitade;
			else
				inicio = mitade;
			mitade = (fin + inicio) / 2;
			upper = alEstadoProb.get(mitade);
			lower = alEstadoProb.get(mitade + 1);
			indice++;
		}
		return upper.nextRepresentant;
	}

	// //////////////////////////////////////////////////////////////////////////
	// DD Cache Maintenance for MDPs
	// //////////////////////////////////////////////////////////////////////////
	// utilizado
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
		// _context.addSpecialNode(_valueDD);

		_context.flushCaches(false);
	}

	// //////////////////////////////////////////////////////////////////////////
	// Miscellaneous helper methods
	// //////////////////////////////////////////////////////////////////////////

	public void checkTimeLimit() throws TimeOutException {
		double elapsed_time = (System.currentTimeMillis() - _lStartTime) / 1000d;
		if (elapsed_time > (double) _nTimeLimitSecs)
			throw new TimeOutException("Elapsed time " + elapsed_time
					+ " (s) exceeded time limit of " + _nTimeLimitSecs + " (s)");
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

}
