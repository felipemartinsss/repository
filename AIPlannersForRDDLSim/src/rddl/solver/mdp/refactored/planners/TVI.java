package rddl.solver.mdp.refactored.planners;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
 * This class is used to run the Topological Value Iteration algorithm over an
 * MDP.
 * 
 * @author felipemartinsss
 *
 */
public class TVI extends Policy {
	private static boolean ONLY_REACHABILITY_ANALYSIS = false;
	private static boolean ONLY_BISIMULATION = false;
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;
	private static int MINUTE = 60;
	// Field used to verify LRTDP algorithm convergence.
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
	// private HashMap <ArrayList <Boolean>, Float> previousValueFunction;
	private HashMap<ArrayList<Boolean>, Boolean> solved;
	// private HashMap <ArrayList <Boolean>, Float> previousValueFunction;

	private MDP mdp = null;
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;
	private Integer stochasticBisimulation = -1;
	private Cronometro stochasticBisimulationTime;
	private Hashtable reduceRemapLeavesCache = new Hashtable();
	private Hashtable simplifyPartitionCache = new Hashtable();
	private ArrayList<Integer> primeNumbers = new ArrayList<Integer>();
	private LinkedHashMap<Integer, Boolean> primeUsed = new LinkedHashMap<Integer, Boolean>();
	// needed to represent ADD partitions.
	private HashMap<Integer, Boolean> blockStable = new HashMap<Integer, Boolean>();
	private HashMap<LinkedHashSet<Integer>, ArrayList<Integer>> fluentwisePartitionsUsed = new HashMap<LinkedHashSet<Integer>, ArrayList<Integer>>();
	private ArrayList<Boolean> initialState;

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
	private HashMap<ArrayList<Boolean>, Boolean> discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();

	private HashMap<ArrayList<Boolean>, Double> lowerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, Double> uppeerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, HashSet<Action>> applicableActions = new HashMap<ArrayList<Boolean>, HashSet<Action>>();

	private HashMap<ArrayList<Boolean>, Boolean> stateVisited = new HashMap<ArrayList<Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, String> optimalPolicy;

	private Cronometro tviTime;
	private int numberOfComponents;
	private HashMap<ArrayList<Boolean>, Double> lastValueFunction;
	private HashMap<ArrayList<Boolean>, Double> currentValueFunction;
	private HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>> _hmStateTransition = new HashMap<Pair<ArrayList, Action>, ArrayList<ProbState>>();

	private String SEPARATOR;
	private double initialStateValue;

	// Constructors
	public TVI() {
	}

	public TVI(String instance_name) {
		super(instance_name);
	}

	/**
	 * Visits the MDP state with a strategy known as depth search and fills a
	 * list of adjacency based on the MDP states.
	 */
	public void depthFirstSearch(
			ArrayList<Boolean> state,
			int currentHorizon,
			Stack<ArrayList<Boolean>> stackOfStates,
			HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {

		if (discoveredStates.get(state) == null) {
			discoveredStates.put(state, false);
			if (adjacencyList.get(state) == null) {
				adjacencyList.put(state, new HashSet<ArrayList<Boolean>>());
			}

			if (applicableActions.get(state) == null) {
				HashSet<Action> actions = new HashSet<Action>(
						_hmActionName2Action.values());
				applicableActions.put(state, actions);
			}

			// for (Action a : _hmActionName2Action.values()) {
			for (Action a : applicableActions.get(state)) {
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				ArrayList<ProbState> transicoes = computeSuccesorsEnum(atribb,
						a._hmVarID2CPT);
				for (int i = 0; i < transicoes.size(); i++) {
					ArrayList<Boolean> nextState = transicoes.get(i).nextRepresentant;
					// adiciona nextState como um estado vizinho de state
					adjacencyList.get(state).add(nextState);
					if (discoveredStates.get(nextState) == null) {
						depthFirstSearch(nextState, currentHorizon + 1,
								stackOfStates, adjacencyList);
					}
				}
			}
			discoveredStates.put(state, true);
		}
		stackOfStates.push(state);
	}

	/**
	 * Computes a transposed adjacency list based on an adjacency list. That is,
	 * if exists P(s'|s,a) in the adjacency list, in the transposed adjacency
	 * list we should have P(s|s',a).
	 */
	public HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> getTransposedAdjacencyList(
			HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> transposedAdjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		for (ArrayList<Boolean> state : adjacencyList.keySet()) {
			HashSet<ArrayList<Boolean>> successors = adjacencyList.get(state);
			for (ArrayList<Boolean> eachSuccessor : successors) {
				HashSet<ArrayList<Boolean>> transposedSuccessors = transposedAdjacencyList
						.get(eachSuccessor);
				if (transposedSuccessors == null) {
					transposedSuccessors = new HashSet<ArrayList<Boolean>>();
				}
				transposedSuccessors.add(state);
				transposedAdjacencyList
						.put(eachSuccessor, transposedSuccessors);
			}
		}
		return transposedAdjacencyList;
	}

	/**
	 * The following to structures are useful to show to Topological Value
	 * Iteration which states should be updated together.
	 */
	private HashMap<ArrayList<Boolean>, Integer> stateToSCCId = new HashMap<ArrayList<Boolean>, Integer>();
	private HashMap<Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap<Integer, ArrayList<ArrayList<Boolean>>>();
	private HashMap<Integer, Integer> stronglyConnectedComponentsDDs = new HashMap<Integer, Integer>();

	/**
	 * The Kosaraju's algorithm. Used to find the strongly connected components
	 * (SCCs).
	 * 
	 * @param add_state_assign_clone
	 * @return
	 */
	public int kosaraju(ArrayList<Boolean> add_state_assign_clone) {
		Integer numberOfComponents = 0;

		HashMap<ArrayList<Boolean>, Boolean> stateExpanded = new HashMap<ArrayList<Boolean>, Boolean>();

		Stack<ArrayList<Boolean>> stackOfStates = new Stack<ArrayList<Boolean>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> transposedAdjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		depthFirstSearch((ArrayList<Boolean>) add_state_assign_clone, 0,
				stackOfStates, adjacencyList);
		transposedAdjacencyList = getTransposedAdjacencyList(adjacencyList);
		while (!stackOfStates.isEmpty()) {
			Integer componentDD = _context.getConstantNode(0);
			// System.out.println("Outer Iterations = " + iterations++);
			ArrayList<Boolean> state = stackOfStates.pop();
			Stack<ArrayList<Boolean>> territory = new Stack<ArrayList<Boolean>>();

			// se for um estado que ainda n�o foi visitado.
			if (SCCIdToMetaStates.get(numberOfComponents) == null) {
				ArrayList<ArrayList<Boolean>> metaState = new ArrayList<ArrayList<Boolean>>();
				metaState.add(state);
				SCCIdToMetaStates.put(numberOfComponents, metaState);
				stateToSCCId.put(state, numberOfComponents);
				stateExpanded.put(state, true);
				territory.push(state);
				componentDD = DDUtils.UpdateValue(_context, componentDD, state,
						numberOfComponents + 1);
			}

			while (!territory.isEmpty()) {
				state = territory.pop();

				if (stackOfStates.contains(state)) {
					stackOfStates.remove(state);
				}

				// representar SCC como ADD para tornar mais eficiente.
				// the next loop must be in the transposed adjacency list.
				HashSet<ArrayList<Boolean>> listForCurrentState = transposedAdjacencyList
						.get(state);
				if (listForCurrentState != null) {
					for (ArrayList<Boolean> nextState : listForCurrentState) {

						if (stateExpanded.get(nextState) == null
								&& stateToSCCId.get(nextState) == null) {
							ArrayList<ArrayList<Boolean>> metaState = SCCIdToMetaStates
									.get(numberOfComponents);
							metaState.add(nextState);
							SCCIdToMetaStates
									.put(numberOfComponents, metaState);
							stateToSCCId.put(nextState, numberOfComponents);
							stateExpanded.put(nextState, true);
							territory.push(nextState);
						}

						if (stackOfStates.contains(nextState)) {
							stackOfStates.remove(nextState);
						}
					}
				}
			}
			stronglyConnectedComponentsDDs.put(numberOfComponents + 1,
					componentDD);
			// _context.getGraph(componentDD).launchViewer();
			numberOfComponents++;
		}
		return numberOfComponents;
	}

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
			// previousValueFunction = new HashMap <ArrayList <Boolean>, Float>
			// ();
			valueFunction = new HashMap<ArrayList<Boolean>, Double>();
			solved = new HashMap<ArrayList<Boolean>, Boolean>();
			tviTime = new Cronometro();
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
			reachabilityTime = new Cronometro();

			// Topological Value Iteration
			tviTime.setStart();
			numberOfComponents = kosaraju(add_state_assign_clone);
			topologicalvalueIteration(add_state_assign_clone,
					numberOfComponents, stateToSCCId, SCCIdToMetaStates);
			tviTime.setEnd();
			
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

		}

		getActionCounter++;
		if (getActionCounter == 40) {
			getActionTimer.setEnd();
		}
		return action_map.get(action_taken);
	}

	private void topologicalvalueIteration(
			ArrayList<Boolean> add_state_assign_clone, int numberOfComponents,
			HashMap<ArrayList<Boolean>, Integer> stateToSCCId,
			HashMap<Integer, ArrayList<ArrayList<Boolean>>> sCCIdToMetaStates) {
		initialState = add_state_assign_clone;
		for (int i = numberOfComponents - 1; i >= 0; i--) {
			ArrayList<ArrayList<Boolean>> statesInCurrentComponent = sCCIdToMetaStates
					.get(new Integer(i));
			valueIteration(statesInCurrentComponent);
		}

		// initialStateValue = _context.evaluate(valueFunctionVI, initialState);
		initialStateValue = currentValueFunction.get(initialState);

	}

	public void valueIteration(
			ArrayList<ArrayList<Boolean>> statesInCurrentComponent) {

		if (optimalPolicy == null) {
			optimalPolicy = new HashMap<ArrayList<Boolean>, String>();
		}

		if (lastValueFunction == null) {
			lastValueFunction = new HashMap<ArrayList<Boolean>, Double>();
		}

		if (currentValueFunction == null) {
			currentValueFunction = new HashMap<ArrayList<Boolean>, Double>();
		}

		for (ArrayList<Boolean> state : statesInCurrentComponent) {
			currentValueFunction.put(state, 0.0d);
		}

		while (true) {
			double currentMaxError = 0.0d;
			double stateError;
			for (ArrayList<Boolean> state : statesInCurrentComponent) {

				double stateLastValue = currentValueFunction.get(state);
				lastValueFunction.put(state, stateLastValue);

				HashMap<Action, Double> qValues = new HashMap<Action, Double>();
				Double bestQValue = -Double.MAX_VALUE;
				for (Action a : applicableActions.get(state)) {
					state.clone();

					Pair stateAction = new Pair(state, a);
					ArrayList<ProbState> transicoes = _hmStateTransition
							.get(stateAction);
					if (transicoes == null) {
						transicoes = computeSuccesorsEnum(state, a._hmVarID2CPT);
						_hmStateTransition.put(stateAction, transicoes);
					}

					Double currentActionValue = 0.0d;
					for (int i = 0; i < transicoes.size(); i++) {
						ProbState probState = transicoes.get(i);
						currentActionValue += probState._dProb
								* currentValueFunction
										.get(probState.nextRepresentant);
					}
					currentActionValue = _context.evaluate(a._reward, state)
							+ _dDiscount * currentActionValue;
					qValues.put(a, currentActionValue);
					if (bestQValue < currentActionValue) {
						bestQValue = currentActionValue;
						optimalPolicy.put(state, a._csActionName.toString());
					}
				}
				currentValueFunction.put(state, bestQValue);
				stateError = Math.abs(currentValueFunction.get(state)
						- lastValueFunction.get(state));
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

	private ArrayList<ProbState> computeSuccesorsEnum(ArrayList state,
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
		// alEstadoProb.get(0)._dProb = 1;
		// alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		return alEstadoProb;
	}

	public void roundEnd(double reward) {
		super.roundEnd(reward);
		new StochasticBisimulationCommons().timeInfo("TVI_Time", _sInstanceName,
				initialStateValue, tviTime, reward);
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
	}
}
