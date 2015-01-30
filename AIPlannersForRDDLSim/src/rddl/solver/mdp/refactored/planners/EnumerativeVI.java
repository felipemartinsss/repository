package rddl.solver.mdp.refactored.planners;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
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
import util.ActionTransition;
import util.CString;
import util.Cronometro;
import util.MDP;
import util.Pair;
import util.ProbState;
import util.StochasticBisimulationCommons;
import dd.discrete.ADD;
import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;

/**
 * Enumerative VI is an implementation of this planner for RDDLSim.
 * 
 * @author felipemartinsss
 *
 */
public class EnumerativeVI extends Policy {
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;

	// Par�metro utilizado para verificar a converg�ncia do algoritmo LRTDP.
	private double maximumBellmanError = 0.001d; // 10^(-3)
	private int getActionCounter = 0;
	private Cronometro getActionTimer;
	private int reachableStates = 0;
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
	private MDP mdp = null;
	// private Politica pi = null;
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;
	private Integer stochasticBisimulation = -1;
	private ArrayList<Integer> primeNumbers = new ArrayList<Integer>();
	private LinkedHashMap<Integer, Boolean> primeUsed = new LinkedHashMap<Integer, Boolean>();
	// needed to represent ADD partitions.
	private HashMap<Integer, Boolean> blockStable = new HashMap<Integer, Boolean>();
	private HashMap<LinkedHashSet<Integer>, ArrayList<Integer>> fluentwisePartitionsUsed = new HashMap<LinkedHashSet<Integer>, ArrayList<Integer>>();
	private Cronometro viTime;

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
	private HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>> _hmStateTransition = new HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>>();
	private HashMap<ArrayList<Boolean>, Double> lastValueFunction;
	private HashMap<ArrayList<Boolean>, Double> currentValueFunction;
	private Integer multCPTs = -1;
	private Integer succss = -1;
	private String SEPARATOR;
	private int currentLayer = -1;
	private HashMap<ArrayList<Boolean>, Boolean> discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();

	private HashMap<ArrayList<Boolean>, Integer> stateToSCCId = new HashMap<ArrayList<Boolean>, Integer>();
	private HashMap<Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap<Integer, ArrayList<ArrayList<Boolean>>>();
	private HashMap<Integer, Integer> stronglyConnectedComponentsDDs = new HashMap<Integer, Integer>();

	private HashMap<ArrayList<Boolean>, Double> lowerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, Double> uppeerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, HashSet<Action>> applicableActions = new HashMap<ArrayList<Boolean>, HashSet<Action>>();

	private HashMap<ArrayList<Boolean>, Boolean> stateVisited = new HashMap<ArrayList<Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, String> optimalPolicy;

	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private HashSet<Action> actionsVerified = new HashSet<Action>();
	private LinkedList<Double> allLeavesValues = new LinkedList<Double>();
	private double initialStateValue;

	// Constructores
	public EnumerativeVI() {
	}

	public EnumerativeVI(String instance_name) {
		super(instance_name);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
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

		// compute the Enumerated VI
		if (getActionCounter == 0) {
			viTime = new Cronometro();
			viTime.setStart();
			ArrayList<ArrayList<Boolean>> allMDPStates = getAllStates();
			valueIteration(allMDPStates);
			// initialStateValue = _context.evaluate(valueFunctionVI,
			// add_state_assign_clone);
			initialStateValue = currentValueFunction
					.get(add_state_assign_clone);
			viTime.setEnd();
			
			// Remove the call below if you want to  see the results of Simulator class.
			System.exit(0);
		}

		// Get a map of { legal action names -> RDDL action definition }
		Map<String, ArrayList<PVAR_INST_DEF>> action_map = ActionGenerator
				.getLegalBoolActionMap(s);

		// Use the precomputed q-functions (cached when the value function
		// was computed) to determine the best action for this state
		String action_taken = null;
		if (optimalPolicy == null) {
			// No VI results available, just take random action
			ArrayList<String> actions = new ArrayList<String>(
					action_map.keySet());
			action_taken = actions.get(_rand.nextInt(actions.size()));

			if (SHOW_ACTION_TAKEN)
				System.out.println("\n--> [Random] action taken: "
						+ action_taken);
		} else {
			ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) stateAssign
					.clone();
			stateAssignClone.remove(0);
			action_taken = optimalPolicy.get(stateAssignClone);
			System.out.println("action_taken = " + action_taken);
		}

		getActionCounter++;

		return action_map.get(action_taken);
	}

	/**
	 * Method that gets all MDP states, that is, the states to be updated by
	 * Value Iteration Algorithm.
	 */
	public ArrayList<ArrayList<Boolean>> getAllStates() {
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		for (int i = 0; i < (_translation._alStateVars.size() + 1) * 2; i++) {
			// for (int i = 0; i <= _translation._alStateVars.size(); i++) {
			assign.add(null);
		}

		Stack<ArrayList<Boolean>> listaMapeamentos = new Stack<ArrayList<Boolean>>();
		listaMapeamentos.add(assign);

		int tamEstadoAtual = assign.size() / 2;
		// int tamEstadoAtual = assign.size();
		for (int i = 0; i < listaMapeamentos.size(); i++) {
			ArrayList<Boolean> atribuicao = listaMapeamentos.get(i);
			for (int j = 1; j < tamEstadoAtual; j++) {
				if (atribuicao.get(j) == null) {
					ArrayList<Boolean> variacaoTAtribuicao = (ArrayList<Boolean>) atribuicao
							.clone();
					ArrayList<Boolean> variacaoFAtribuicao = (ArrayList<Boolean>) atribuicao
							.clone();
					variacaoTAtribuicao.set(j, true);
					listaMapeamentos.add(variacaoTAtribuicao);
					variacaoFAtribuicao.set(j, false);
					listaMapeamentos.add(variacaoFAtribuicao);
					break;
				}
			}
		}

		Double dTotalOfStates = Math.pow(2.0d, new Double(
				_translation._alStateVars.size()));
		Integer iTotalOfStates = dTotalOfStates.intValue();
		ArrayList<ArrayList<Boolean>> setOfStates = new ArrayList<ArrayList<Boolean>>();

		for (int i = listaMapeamentos.size() - 1; i >= listaMapeamentos.size()
				- iTotalOfStates; i--) {
			ArrayList<Boolean> atribuicao = listaMapeamentos.get(i);
			setOfStates.add(atribuicao);
		}

		// System.out.println(setOfStates);
		return setOfStates;
	}

	/**
	 * Planning solution - Value Iteration Algorithm
	 */
	public void valueIteration(
			ArrayList<ArrayList<Boolean>> statesInCurrentComponent) {

		if (optimalPolicy == null) {
			optimalPolicy = new HashMap<ArrayList<Boolean>, String>();
		}

		lastValueFunction = new HashMap<ArrayList<Boolean>, Double>();
		currentValueFunction = new HashMap<ArrayList<Boolean>, Double>();
		for (ArrayList<Boolean> state : statesInCurrentComponent) {
			ArrayList<Boolean> attrib = (ArrayList<Boolean>) state.clone();
			attrib.remove(0);
			currentValueFunction.put(attrib, 0.0d);
		}

		while (true) {
			double currentMaxError = 0.0d;
			double stateError;

			for (ArrayList<Boolean> state : statesInCurrentComponent) {

				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb.remove(0);

				double stateLastValue = currentValueFunction.get(atribb);
				lastValueFunction.put(atribb, stateLastValue);

				HashMap<Action, Double> qValues = new HashMap<Action, Double>();
				Double bestQValue = -Double.MAX_VALUE;

				for (Action a : _hmActionName2Action.values()) {
					Pair stateAction = new Pair(atribb, a);
					ArrayList<ProbState> transicoes = _hmStateTransition
							.get(stateAction);
					if (transicoes == null) {
						transicoes = computeSuccesorsEnum(atribb,
								a._hmVarID2CPT);
						_hmStateTransition.put(stateAction, transicoes);
					}

					Double currentActionValue = 0.0d;
					for (int i = 0; i < transicoes.size(); i++) {
						ProbState probState = transicoes.get(i);
						currentActionValue += probState._dProb
								* currentValueFunction
										.get(probState.nextRepresentant);
					}
					currentActionValue = _context.evaluate(a._reward, atribb)
							+ _dDiscount * currentActionValue;
					qValues.put(a, currentActionValue);
					if (bestQValue < currentActionValue) {
						bestQValue = currentActionValue;
						optimalPolicy.put(atribb, a._csActionName.toString());
					}
				}
				currentValueFunction.put(atribb, bestQValue);
				stateError = Math.abs(currentValueFunction.get(atribb)
						- lastValueFunction.get(atribb));
				currentMaxError = Math.max(currentMaxError, stateError);
			}

			if (currentMaxError < maximumBellmanError) {
				return;
			}
		}
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
					// _dRewardRange = Math.max(_dRewardRange,
					// _context.getMaxValue(a._reward));
					// maxReward = Math.max (maxReward,
					// _context.getMaxValue(a._reward));
					// minReward = Math.min (minReward,
					// _context.getMinValue(a._reward));
				}
				double value_range = _dRewardRange;

				value_range = (_dDiscount < 1d) ? value_range
						/ (1d - _dDiscount) // being lazy: assume infinite
				// horizon
						: _nHorizon * value_range; // assume max reward over
													// horizon*/
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
				}
			}
		}
	}

	/**
	 * Helper method used by computeSuccesorsEnum *
	 * 
	 * @param node
	 * @param assign
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
					// Double probanterior = (alEstadoProb.isEmpty()? 0.0d :
					// alEstadoProb.get(0)._dProb);
					ArrayList<Boolean> newAssign = new ArrayList<Boolean>();
					newAssign.addAll(assign);
					ProbState novoNo = new ProbState(probabilidade, newAssign);
					alEstadoProb.add(0, novoNo);
				}
			}
		}
	}

	/**
	 * Method that returns a set of one step reachable states given a source
	 * state.
	 * 
	 * @param state
	 * @param iD2ADD
	 * @return
	 */
	public ArrayList<ProbState> computeSuccesorsEnum(ArrayList state,
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
		return alEstadoProb;
	}

	/**
	 * Prints the final reward obtained by the planner.
	 */
	public void roundEnd(double reward) {
		super.roundEnd(reward);
		new StochasticBisimulationCommons().timeInfo("VITime", _sInstanceName,
				initialStateValue, viTime, reward);
	}

	/**
	 * Initialize all variables (call before starting value iteration)
	 */
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

	/**
	 * Clear nodes on save list
	 */
	public void clearSaveNodes() {
		_alSaveNodes.clear();
	}

	/**
	 * Remove nodes on save list
	 * 
	 * @param dd
	 */
	public void clearSaveNode(Integer dd) {
		_alSaveNodes.remove(dd);
	}

	/**
	 * Add node to save list
	 * 
	 * @param dd
	 */
	public void saveNode(Integer dd) {
		_alSaveNodes.add(dd);
	}

	/**
	 * Frees up memory... only do this if near limit.
	 */
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
	 * Verifies if the time given to solved the problem already expired. lanca
	 * uma TimeOutException.
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
	 * Show the total memory available to simulator.
	 * 
	 * @return
	 */
	public static String MemDisplay() {
		long total = RUNTIME.totalMemory() / (1024 * 1024);
		long free = RUNTIME.freeMemory() / (1024 * 1024);
		return "Used Memory: " + (total - free) + " MB / Total Memory: "
				+ total + " MB ";
	}

}
