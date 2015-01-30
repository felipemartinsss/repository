package rddl.solver.mdp.refactored.sbisimulation;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Random;
import java.util.TreeSet;

import javax.naming.TimeLimitExceededException;

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
import rddl.solver.mdp.refactored.planners.VIUtils;
import rddl.translate.RDDL2Format;
import util.ActionTransition;
import util.CString;
import util.Cronometro;
import util.MDP;
import util.Pair;
import util.StochasticBisimulationCommons;
import dd.discrete.ADD;
import dd.discrete.ADDDNode;

/**
 * A Value Iteration implementation that is used to solve a reduced model
 * obtained from a stochastic bisimulation. This reduced model has abstract
 * states over all MDP states, even those that are not reachable.
 */
public class MRFSWithValueIteration extends Policy {
	private static boolean ONLY_REACHABILITY_ANALYSIS = false;
	private static boolean ONLY_BISIMULATION = false;
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;
	private static int MINUTE = 60;
	private static int HOUR = 60 * MINUTE;
	private static int DAY = 24 * HOUR;

	private static int AGGREGATION_TIME_LIMIT = 2 * DAY; // Solver time limit
	private static int OFFLINE_SOLVER_TIME_LIMIT = (int) (90 * DAY); // seconds
																		// for
																		// one
																		// OFFLINE
																		// getAction
	private static int ONLINE_SOLVER_TIME_LIMIT = 10; // seconds for one ONLINE
														// getAction

	private static int OFFLINE = 0;
	private static int ONLINE = 1;
	private static int PLANEJAMENTO = OFFLINE;

	// Parameter used to verify algorithm convergence.
	private double maximumBellmanError = 0.001d; // 10^(-3)

	private int getActionCounter = 0;
	private Cronometro getActionTimer;
	private int reachableStates = 0;
	private Cronometro reachabilityTime;
	private HashMap _hmStringPrimeVarID2VarID;
	private HashMap _hmNextVarID2VarID;

	private final static boolean SHOW_STATE = true;
	private final static boolean SHOW_ACTION_TAKEN = true;

	// Only for diagnostics, comment this out when evaluating
	private final static boolean DISPLAY_SPUDD_ADDS_GRAPHVIZ = false;
	private final static boolean DISPLAY_SPUDD_ADDS_TEXT = false;

	private RDDL2Format _translation = null;

	// Using CString wrapper to speedup hash lookups
	private ADD _context;
	private ArrayList<Integer> _allMDPADDs;
	private ArrayList<CString> _alStateVars;
	private ArrayList<CString> _alPrimeStateVars;
	private ArrayList<CString> _alActionNames;
	private HashMap<CString, Action> _hmActionName2Action; // Holds transition
	private HashMap<ArrayList<Boolean>, Double> valueFunction;
	private HashMap<ArrayList<Boolean>, Double> previousValueFunction;
	private HashMap<ArrayList<Boolean>, Boolean> solved;

	private Cronometro valueIterationTime;
	boolean firstTrial = true;

	private MDP mdp = null;
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;
	private Integer stochasticBisimulation = -1;
	private double heuristicaAdmissivel;
	private Cronometro stochasticBisimulationTime;
	private Hashtable reduceRemapLeavesCache = new Hashtable();
	private Hashtable simplifyPartitionCache = new Hashtable();
	private ArrayList<Integer> primeNumbers = new ArrayList<Integer>();
	private LinkedHashMap<Integer, Boolean> primeUsed = new LinkedHashMap<Integer, Boolean>();
	// needed to represent ADD partitions.
	private HashMap<Integer, Boolean> blockStable = new HashMap<Integer, Boolean>();
	private HashMap<LinkedHashSet<Integer>, ArrayList<Integer>> fluentwisePartitionsUsed = new HashMap<LinkedHashSet<Integer>, ArrayList<Integer>>();
	private final static boolean ALWAYS_FLUSH = false; // Always flush DD
														// caches?
	private final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush
																// until < this
																// amt

	// For printing
	private final static DecimalFormat _df = new DecimalFormat("#.###");

	// Timing variables
	private long _lStartTime; // For timing purposes
	private int _nTimeLimitSecs;
	private static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	private INSTANCE _rddlInstance = null;
	private int _valueDD;
	private int _maxDD;
	private int _prevDD;
	private int _nIter;
	private double _dRewardRange; // Important if approximating
	private double _dDiscount;
	private int _nHorizon;
	private ArrayList<Integer> _alSaveNodes; // Nodes to save during cache
	private HashMap<Integer, Integer> _hmPrimeVarID2VarID;

	// Just use the default random seed
	private Random _rand = new Random();
	private HashMap<ArrayList<Boolean>, Integer> stateToSCCId = new HashMap<ArrayList<Boolean>, Integer>();
	private HashMap<Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap<Integer, ArrayList<ArrayList<Boolean>>>();
	private HashMap<ArrayList<Boolean>, Double> lowerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, Double> uppeerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, HashSet<Action>> applicableActions = new HashMap<ArrayList<Boolean>, HashSet<Action>>();
	private HashMap<ArrayList<Boolean>, Boolean> stateVisited = new HashMap<ArrayList<Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, String> optimalPolicy = new HashMap<ArrayList<Boolean>, String>();
	private HashMap<Integer, Integer> stronglyConnectedComponentsDDs = new HashMap<Integer, Integer>();
	private StochasticBisimulationCommons sbc;
	private Integer multCPTs = -1;
	private Integer succss = -1;
	private int currentLayer = -1;
	private double valueFunctionS0;
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private String SEPARATOR;
	private HashMap<Pair<Double, CString>, HashMap<Double, Double>> hashOfProbabilityDistribution = new HashMap<Pair<Double, CString>, HashMap<Double, Double>>();
	private HashSet<Action> actionsVerified = new HashSet<Action>();
	private LinkedList<Double> allLeavesValues = new LinkedList<Double>();
	private HashMap<ArrayList<Boolean>, Boolean> discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();
	private VIUtils viUtils;

	// Constructors
	public MRFSWithValueIteration() {
	}

	public MRFSWithValueIteration(String instance_name) {
		super(instance_name);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			sbc = new StochasticBisimulationCommons(_translation, _context,
					_hmActionName2Action, _alStateVars, false);
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
			previousValueFunction = new HashMap<ArrayList<Boolean>, Double>();
			valueFunction = new HashMap<ArrayList<Boolean>, Double>();
			solved = new HashMap<ArrayList<Boolean>, Boolean>();
			viUtils = new VIUtils(_sInstanceName, mdp);
		}

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

		@SuppressWarnings("rawtypes")
		ArrayList add_state_assign = DDUtils.ConvertTrueVars2DDAssign(_context,
				true_vars, _alStateVars);
		ArrayList<Boolean> stateAssign = (ArrayList<Boolean>) add_state_assign;
		stateAssign.add(0, null);

		ArrayList<Boolean> add_state_assign_clone = (ArrayList<Boolean>) add_state_assign
				.clone();
		add_state_assign_clone.remove(0);

		// compute the Reachability-based model minimization
		if (getActionCounter == 0) {
			stochasticBisimulationTime = new Cronometro();
			
			/*
			reachabilityTime = new Cronometro();
			reachabilityTime.setStart();
			reachableStates = sbc.findReachableStates(
					(ArrayList<Boolean>) add_state_assign_clone, 40);
			reachabilityTime.setEnd();
			*/

			try {
				stochasticBisimulationTime.setStart();
				stochasticBisimulation = sbc
						.getReducedExplicitMDP(AGGREGATION_TIME_LIMIT);
				mdp.setStochasticBisimulation(stochasticBisimulation);
				stochasticBisimulationTime.setEnd();
				// _context.getGraph(stochasticBisimulation).launchViewer();
			} catch (TimeOutException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		ArrayList<Boolean> currentAbstractState = mdp
				.getRepresentant(stateAssign);

		if (currentAbstractState == null) {
			HashSet<ADDDNode> blocos = new HashSet<ADDDNode>();
			_context.collectLeaves(stochasticBisimulation, blocos);
			ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) stateAssign
					.clone();
			stateAssignClone.remove(0);
			double valorBloco = _context.evaluate(stochasticBisimulation,
					stateAssignClone);
			stateAssignClone.add(0, null);
			currentAbstractState = mdp.setRepresentant(valorBloco,
					stateAssignClone);

			if (getActionCounter == 0) {
				HashSet blocosBissimulacao = new HashSet();
				_context.collectLeaves(stochasticBisimulation,
						blocosBissimulacao);
				// System.out.println("N�mero de blocos da bissimula��o estoc�stica: "
				// + blocosBissimulacao.size());
				STOCHASTIC_BISIMULATION_COMPUTED = true;
				primeNumbers.clear();
				primeNumbers = null;
				sbc.getSoe().suggestToFreeMemory();
				flushCaches();
			}

			if (valueFunction.get(currentAbstractState) == null
					&& solved.get(currentAbstractState) == null) {
				valueFunction.put(currentAbstractState, heuristicaAdmissivel);
				solved.put(currentAbstractState, false);
			}
		}

		_lStartTime = System.currentTimeMillis();

		if (getActionCounter == 0) {
			if (ONLY_BISIMULATION) {
				System.out.println("Only bisimulation...");
			} else if (ONLY_REACHABILITY_ANALYSIS) {
				System.out.println("Only reachability analysis...");
			} else {
				try {
					if (PLANEJAMENTO == OFFLINE && getActionCounter == 0) {
						_nTimeLimitSecs = OFFLINE_SOLVER_TIME_LIMIT;
						valueIterationTime = new Cronometro();
						valueIterationTime.setStart();
						viUtils.doValueIteration(currentAbstractState,
								maximumBellmanError, 40);
						valueIterationTime.setEnd();
						valueFunctionS0 = mdp.getValueFunction().get(
								currentAbstractState);
						
						// Remove the call below if you want to  see the results of Simulator class.
						System.exit(0);
					} else if (PLANEJAMENTO == ONLINE) {
						_nTimeLimitSecs = ONLINE_SOLVER_TIME_LIMIT;
						viUtils.doValueIteration(currentAbstractState,
								maximumBellmanError, 40);
					}
				} catch (TimeLimitExceededException e1) {
					e1.printStackTrace();
				}
			}
			// System.exit(0);
		}

		pi = viUtils.getPi();

		// Get a map of { legal action names -> RDDL action definition }
		Map<String, ArrayList<PVAR_INST_DEF>> action_map = ActionGenerator
				.getLegalBoolActionMap(s);

		// Use the precomputed q-functions (cached when the value function
		// was computed) to determine the best action for this state
		String action_taken = null;
		if (pi == null) {
			// No VI results available, just take random action
			ArrayList<String> actions = new ArrayList<String>(
					action_map.keySet());
			action_taken = actions.get(_rand.nextInt(actions.size()));

			if (SHOW_ACTION_TAKEN)
				System.out.println("\n--> [Random] action taken: "
						+ action_taken);
		} else {
			if (SHOW_ACTION_TAKEN)
				System.out.println("\nActions and Q-values:");

			// _context.getGraph(stochasticBisimulation).launchViewer();

			stateAssign.remove(0);
			Double valorBloco = _context.evaluate(stochasticBisimulation,
					stateAssign);
			stateAssign.add(0, null);
			ArrayList<Boolean> representant = mdp.getRepresentant(valorBloco);
			if (representant != null) {
				ActionTransition at = pi.get(representant);
				// System.out.println("Assignments: " + e.getAtribuicoes());
				if (at != null) {
					action_taken = at.getAction()._csActionName._string;
					// System.out.println("Current State: " + representant);
					System.out.println("Melhor acao: " + action_taken);
				} else {
					ArrayList<String> actions = new ArrayList<String>(
							action_map.keySet());
					action_taken = actions.get(_rand.nextInt(actions.size()));
					System.out.println("xxxxxxxxxx ACAO ALEATORIA xxxxxxxxxx: "
							+ action_taken);
				}
			}
		}

		getActionCounter++;
		if (getActionCounter == 40) {
			getActionTimer.setEnd();
		}

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

		String OS = System.getProperty("os.name").toLowerCase();
		if (OS.indexOf("win") >= 0) {
			SEPARATOR = new String("\\");
		}

		if (OS.indexOf("nix") >= 0 || OS.indexOf("nux") >= 0
				|| OS.indexOf("aix") >= 0) {
			System.out.println("OS = Unix");
			SEPARATOR = new String("/");
		}

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
				// System.out.println ("Current action: " + a);
				HashMap<CString, Integer> cpts = new HashMap<CString, Integer>();
				int reward = _context.getConstantNode(0d);

				// Build reward from additive decomposition
				ArrayList<Integer> reward_summands = _translation._act2rewardDD
						.get(a);
				for (int summand : reward_summands)
					reward = _context.applyInt(reward, summand, ADD.ARITH_SUM);
				_allMDPADDs.add(reward);

				// print the reward function for this action
				// _translation._context.getGraph(reward).launchViewer();

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

					// show the dd_true, used for stochastic bisimulation.
					// System.out.println("Current state var: " + s);
					// _context.getGraph(dd_true).launchViewer();

					// Now have "dual action diagram" cpt DD
					int cpt = _context.applyInt(dd_true, dd_false,
							ADD.ARITH_SUM);

					cpts.put(new CString(s + "'"), cpt);
					_allMDPADDs.add(cpt);

					// System.out.println("Current variable: " + s + "'");
					// Show the decision diagram for the next state variable
					// _translation._context.getGraph(cpt).launchViewer();
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

			try {
				resetSolver();

				for (Action a : _hmActionName2Action.values()) {
					_dRewardRange = Math.max(_dRewardRange,
							_context.getMaxValue(a._reward));
				}
				double value_range = _dRewardRange;

				value_range = (_dDiscount < 1d) ? value_range
						/ (1d - _dDiscount) // being lazy: assume infinite
				// horizon
						: _nHorizon * value_range; // assume max reward over
													// horizon*/

				heuristicaAdmissivel = value_range;

			} catch (Exception e) {
				System.err.println("Exception at " + _nIter + " iterations.");
				e.printStackTrace(System.err);
				System.exit(1);
			} catch (Throwable t) {
				System.out
						.println("Throwable lan�ado. Subclasse de java.lang.Error: "
								+ t.getMessage());
				t.printStackTrace();
			} finally {
				if (mdp == null) {
					mdp = new MDP();
					mdp.setFatorDeDesconto((float) _dDiscount);
					float gamma = mdp.getFatorDeDesconto();
					if (gamma == 1.0f) {
						gamma = 0.99f;
						mdp.setFatorDeDesconto(0.99f);
					}
					mdp.setErroMaximoPermitido((float) maximumBellmanError);
					if (pi == null) {
						pi = new HashMap<ArrayList<Boolean>, ActionTransition>();
					}

					mdp.set_alActionNames(_alActionNames);
					mdp.set_allMDPADDs(_allMDPADDs);
					mdp.set_alPrimeStateVars(_alPrimeStateVars);
					mdp.set_alStateVars(_alStateVars);
					mdp.set_context(_context);
					mdp.set_dDiscount(_dDiscount);
					mdp.set_hmActionName2Action(_hmActionName2Action);
					mdp.set_hmPrimeVarID2VarID(_hmPrimeVarID2VarID);
					mdp.set_translation(_translation);
				}
			}
		}
	}

	/**
	 * Prints the final reward.
	 */
	public void roundEnd(double reward) {
		super.roundEnd(reward);
		sbc.plannerTimeInfo(_sInstanceName, reachabilityTime,
				stochasticBisimulationTime, valueIterationTime, reward,
				valueFunctionS0, "MRFSWithValueIteration");
	}

	// Initialize all variables (call before starting value iteration)
	public void resetSolver() {
		_prevDD = _maxDD = -1;
		_valueDD = _context.getConstantNode(0d); // Initialize to 0
		_nIter = -1;
		_rddlInstance = _rddl._tmInstanceNodes.get(this._sInstanceName);
		if (_rddlInstance == null) {
			System.err.println("ERROR: Could not fine RDDL instance '"
					+ _rddlInstance + "'");
			System.exit(1);
		}

		_dDiscount = _rddlInstance._dDiscount;
		if (_dDiscount == 1.0d) {
			_dDiscount = 0.99d;
		}
		_nHorizon = _rddlInstance._nHorizon;

		_hmPrimeVarID2VarID = new HashMap<Integer, Integer>();
		_hmStringPrimeVarID2VarID = new HashMap();
		_hmNextVarID2VarID = new HashMap();
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
			_hmStringPrimeVarID2VarID.put(var_prime, var);
			_hmStringPrimeVarID2VarID.put(var, var_prime);
			_hmNextVarID2VarID.put(var_prime, var);
			_hmNextVarID2VarID.put(var, var);
		}

		_alSaveNodes = new ArrayList<Integer>();

		_dRewardRange = -Double.MAX_VALUE;
		for (Action a : _hmActionName2Action.values())
			_dRewardRange = Math.max(
					_dRewardRange,
					_context.getMaxValue(a._reward)
							- _context.getMinValue(a._reward));
	}

	// //////////////////////////////////////////////////////////////////////////
	// DD Cache Maintenance for MDPs
	// //////////////////////////////////////////////////////////////////////////

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
		_context.addSpecialNode(_valueDD);
		if (_maxDD != -1)
			_context.addSpecialNode(_maxDD);
		if (_prevDD != -1)
			_context.addSpecialNode(_prevDD);

		if (!STOCHASTIC_BISIMULATION_COMPUTED) {
			_context.addSpecialNode(reachableStates);
			_context.addSpecialNode(currentLayer);
			if (multCPTs != -1) {
				_context.addSpecialNode(multCPTs);
			}

			if (succss != -1) {
				_context.addSpecialNode(succss);
			}
		} else {
			_context.addSpecialNode(stochasticBisimulation);
		}

		_context.flushCaches(true);
	}

	// //////////////////////////////////////////////////////////////////////////
	// Miscellaneous helper methods
	// //////////////////////////////////////////////////////////////////////////

	/**
	 * Verifica se o tempo dado para resolver o problema ja expirou. Se sim,
	 * lanca uma TimeOutException.
	 * 
	 * @throws TimeOutException
	 */
	public void checkTimeLimit() throws TimeOutException {
		double elapsed_time = (System.currentTimeMillis() - _lStartTime) / 1000d;
		if (elapsed_time > (double) _nTimeLimitSecs)
			throw new TimeOutException("Elapsed time " + elapsed_time
					+ " (s) exceeded time limit of " + _nTimeLimitSecs + " (s)");
	}

	/**
	 * Exibe a "memoria total reservada ao Simulador : memoria disponivel".
	 * 
	 * @return
	 */
	public static String MemDisplay() {
		long total = RUNTIME.totalMemory() / (1024 * 1024);
		long free = RUNTIME.freeMemory() / (1024 * 1024);
		return "Used Memory: " + (total - free) + " MB / Total Memory: "
				+ total + " MB ";
	}

	/**
	 * Ajusta o limite de tempo dado ao simulador.
	 */
	public void setLimitTime(Integer time) {
		AGGREGATION_TIME_LIMIT = time;
	}
}