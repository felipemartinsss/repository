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
import java.util.Stack;
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
 * A Topological Value Iteration implementation that is used to solve a 
 * reduced model obtained from a stochastic bisimulation.
 * This reduced model has only reachable MDP states given 
 * an initial state s0.
 */
public class ReachMRFSWithTopologicalValueIteration extends Policy {

	private StochasticBisimulationCommons sbc;

	private static boolean ONLY_REACHABILITY_ANALYSIS = false;
	private static boolean ONLY_BISIMULATION = false;
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;
	private final static int VI = 0;
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

	// Par�metro utilizado para verificar a converg�ncia do algoritmo LRTDP.
	private double maximumBellmanError = 0.001d; // 10^(-3)

	private int getActionCounter = 0;
	private Cronometro getActionTimer;
	private int reachableStates = 0;
	private Cronometro reachabilityTime;
	private Cronometro sccFinderTime;
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
	// private HashMap <ArrayList <Boolean>, Float> previousValueFunction;

	private Cronometro lrtdpTime;
	private MDP mdp = null;
	// private Politica pi = null;
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;
	private Integer stochasticBisimulation = -1;
	private double heuristicaAdmissivel;
	private Cronometro stochasticBisimulationTime;
	private Cronometro topologicalValueIterationTime;
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
	private int tamanhoDaPilha = 0;
	
	// The following structured are needed to show TVI which states should be updated together.
	private HashMap<ArrayList<Boolean>, Integer> stateToSCCId = new HashMap<ArrayList<Boolean>, Integer>();
	private HashMap<Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap<Integer, ArrayList<ArrayList<Boolean>>>();
	private HashMap<ArrayList<Boolean>, Double> lowerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, Double> uppeerBounds = new HashMap<ArrayList<Boolean>, Double>();
	private HashMap<ArrayList<Boolean>, HashSet<Action>> applicableActions = new HashMap<ArrayList<Boolean>, HashSet<Action>>();
	private int valueFunctionUpperBounds;
	private HashMap<ArrayList<Boolean>, Boolean> stateVisited = new HashMap<ArrayList<Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, String> optimalPolicy = new HashMap<ArrayList<Boolean>, String>();
	private HashMap<Integer, Integer> stronglyConnectedComponentsDDs = new HashMap<Integer, Integer>();
	private int numberOfComponents;
	private Integer multCPTs = -1;
	private Integer succss = -1;
	private int currentLayer = -1;
	private LinkedHashMap<Integer, ArrayList<ArrayList<Boolean>>> statesByTopologicalOrder;
	private double valueFunctionS0;
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private String SEPARATOR;
	private HashMap<Pair<Double, CString>, HashMap<Double, Double>> hashOfProbabilityDistribution = new HashMap<Pair<Double, CString>, HashMap<Double, Double>>();
	private HashSet<Action> actionsVerified = new HashSet<Action>();
	private LinkedList<Double> allLeavesValues = new LinkedList<Double>();
	private HashMap<ArrayList<Boolean>, Boolean> discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();

	// Constructors
	public ReachMRFSWithTopologicalValueIteration() {
	}

	public ReachMRFSWithTopologicalValueIteration(String instance_name) {
		super(instance_name);
	}

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			sbc = new StochasticBisimulationCommons(_translation, _context,
					_hmActionName2Action, _alStateVars, true);
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
			previousValueFunction = new HashMap<ArrayList<Boolean>, Double>();
			valueFunction = new HashMap<ArrayList<Boolean>, Double>();
			solved = new HashMap<ArrayList<Boolean>, Boolean>();
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
			reachabilityTime.setStart();
			reachableStates = sbc.findReachableStates(
					(ArrayList<Boolean>) add_state_assign_clone, 40);
			reachabilityTime.setEnd();
			try {
				stochasticBisimulationTime.setStart();
				stochasticBisimulation = sbc
						.getReducedExplicitMDP(AGGREGATION_TIME_LIMIT);
				stochasticBisimulationTime.setEnd();
				// _context.getGraph(stochasticBisimulation).launchViewer();
			} catch (TimeOutException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			sccFinderTime = new Cronometro();
			sccFinderTime.setStart();
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
			}
			// System.out.println("Computing strongly connected components...");
			numberOfComponents = kosaraju(currentAbstractState);
			sccFinderTime.setEnd();

			// System.out.println("Number of components found in kosaraju algorithm: "
			// + numberOfComponents);
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
						topologicalValueIterationTime = new Cronometro();
						topologicalValueIterationTime.setStart();
						// resolve o MDP reduzido com base nas suas componentes
						// fortemente conexas.
						doTopologicalValueIteration(currentAbstractState,
								maximumBellmanError, 40,
								stronglyConnectedComponentsDDs);
						topologicalValueIterationTime.setEnd();
						
						// Remove the call below if you want to  see the results of Simulator class.
						System.exit(0);
					} else if (PLANEJAMENTO == ONLINE) {
						_nTimeLimitSecs = ONLINE_SOLVER_TIME_LIMIT;
						doTopologicalValueIteration(currentAbstractState,
								maximumBellmanError, 40,
								stronglyConnectedComponentsDDs);
					}
					valueFunctionS0 = valueFunction.get(currentAbstractState);
				} catch (TimeLimitExceededException e1) {
					e1.printStackTrace();
				}
			}
			// System.exit(0);
		}
		
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

	/**
	 * An iterative Depth-First Search (DFS).
	 * @param state
	 * @param currentHorizon
	 * @param stackOfStates
	 * @param adjacencyList
	 */
	public void depthFirstSearchInReducedMDP_ITER(
			ArrayList<Boolean> state,
			int currentHorizon,
			Stack<ArrayList<Boolean>> stackOfStates,
			HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {
		discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();
		// System.out.println("Tamanho da pilha = " + tamanhoDaPilha);
		Stack<ArrayList<Boolean>> algorithmStack = new Stack<ArrayList<Boolean>>();
		algorithmStack.push(state);
		while (!algorithmStack.isEmpty()) {
			state = algorithmStack.pop();
			if (discoveredStates.get(state) == null
					|| discoveredStates.get(state).equals(false)) {
				discoveredStates.put(state, true);
				if (adjacencyList.get(state) == null) {
					adjacencyList.put(state, new HashSet<ArrayList<Boolean>>());
				}

				for (CString a : _hmActionName2Action.keySet()) {
					Action action = _hmActionName2Action.get(a);
					ActionTransition acao = new ActionTransition(action,
							new ArrayList<ProbState>());
					if (!acaoDisponivel(state, action)) {
						ArrayList<Boolean> atribb = (ArrayList<Boolean>) state
								.clone();
						atribb = new ArrayList<Boolean>(atribb.subList(1,
								state.size()));

						double recompensa = _context.evaluate(action._reward,
								atribb);

						acao.setReward(recompensa);

						ArrayList<ProbState> transicoes = computeSuccessorsProbEnum(
								atribb, action._hmVarID2CPT,
								action._csActionName, true);
						acao.setTransitions(transicoes);
						ArrayList<ActionTransition> acoesDisponiveis = enabledActions
								.get(state);
						if (acoesDisponiveis == null) {
							acoesDisponiveis = new ArrayList<ActionTransition>();
						}
						acoesDisponiveis.add(acao);
						enabledActions.put(state, acoesDisponiveis);
					} else {
						acao = getAcao(state, action);
					}

					ArrayList<ProbState> transicoes = acao.getTransitions();
					for (int i = 0; i < transicoes.size(); i++) {
						ArrayList<Boolean> nextState = transicoes.get(i).nextRepresentant;

						// adiciona nextState como um estado vizinho de state
						if (adjacencyList.get(nextState) == null) {
							adjacencyList.put(nextState,
									new HashSet<ArrayList<Boolean>>());
						}
						adjacencyList.get(state).add(nextState);

						if (discoveredStates.get(nextState) == null) {
							discoveredStates.put(nextState, false);
							algorithmStack.push(nextState);
						}
					}
				}
				stackOfStates.push(state);
				// flushCaches();
			}
		}
	}

	/**
	 * A recursive Depth-First Search algorithm for MDPs.
	 */
	public void depthFirstSearchInReducedMDP(
			ArrayList<Boolean> state,
			int currentHorizon,
			Stack<ArrayList<Boolean>> stackOfStates,
			HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {

		System.out.println("Tamanho da pilha = " + tamanhoDaPilha);
		if (discoveredStates.get(state) == null) {
			discoveredStates.put(state, true);
			if (adjacencyList.get(state) == null) {
				adjacencyList.put(state, new HashSet<ArrayList<Boolean>>());
			}

			for (CString a : _hmActionName2Action.keySet()) {
				Action action = _hmActionName2Action.get(a);
				ActionTransition acao = new ActionTransition(action,
						new ArrayList<ProbState>());
				if (!acaoDisponivel(state, action)) {
					ArrayList<Boolean> atribb = (ArrayList<Boolean>) state
							.clone();
					atribb = new ArrayList<Boolean>(atribb.subList(1,
							state.size()));

					double recompensa = _context.evaluate(action._reward,
							atribb);

					acao.setReward(recompensa);

					ArrayList<ProbState> transicoes = computeSuccessorsProbEnum(
							atribb, action._hmVarID2CPT, action._csActionName,
							true);
					acao.setTransitions(transicoes);
					ArrayList<ActionTransition> acoesDisponiveis = enabledActions
							.get(state);
					if (acoesDisponiveis == null) {
						acoesDisponiveis = new ArrayList<ActionTransition>();
					}
					acoesDisponiveis.add(acao);
					enabledActions.put(state, acoesDisponiveis);
				} else {
					acao = getAcao(state, action);
				}

				ArrayList<ProbState> transicoes = acao.getTransitions();
				for (int i = 0; i < transicoes.size(); i++) {
					ArrayList<Boolean> nextState = transicoes.get(i).nextRepresentant;

					// adiciona nextState como um estado vizinho de state
					adjacencyList.get(state).add(nextState);
					if (discoveredStates.get(nextState) == null) {
						tamanhoDaPilha++;
						depthFirstSearchInReducedMDP(nextState,
								currentHorizon + 1, stackOfStates,
								adjacencyList);
					}
				}
			}
			stackOfStates.push(state);
			tamanhoDaPilha--;
		}
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
			for (ArrayList<Boolean> successor : successors) {
				HashSet<ArrayList<Boolean>> transposedSuccessors = transposedAdjacencyList
						.get(successor);
				if (transposedSuccessors == null) {
					transposedSuccessors = new HashSet<ArrayList<Boolean>>();
				}
				transposedSuccessors.add(state);
				transposedAdjacencyList.put(successor, transposedSuccessors);
			}
		}
		return transposedAdjacencyList;
	}

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

		statesByTopologicalOrder = new LinkedHashMap<Integer, ArrayList<ArrayList<Boolean>>>();

		discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();

		Stack<ArrayList<Boolean>> stackOfStates = new Stack<ArrayList<Boolean>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> transposedAdjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		tamanhoDaPilha++;
		// depthFirstSearchInReducedMDP((ArrayList <Boolean>)
		// add_state_assign_clone, 0, stackOfStates, adjacencyList);
		depthFirstSearchInReducedMDP_ITER(
				(ArrayList<Boolean>) add_state_assign_clone, 0, stackOfStates,
				adjacencyList);
		transposedAdjacencyList = getTransposedAdjacencyList(adjacencyList);

		// System.out.println("Already computed the reachability list and its transposed version...");
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
				ArrayList<ArrayList<Boolean>> statesInCurrentComponent = statesByTopologicalOrder
						.get(numberOfComponents + 1);
				if (statesInCurrentComponent == null) {
					statesInCurrentComponent = new ArrayList<ArrayList<Boolean>>();
				}
				ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state
						.clone();
				// stateClone.add(0, null);
				statesInCurrentComponent.add(stateClone);
				statesByTopologicalOrder.put(numberOfComponents + 1,
						statesInCurrentComponent);

				// _context.getGraph(componentDD).launchViewer();
			}

			while (!territory.isEmpty()) {
				state = territory.pop();

				if (stackOfStates.contains(state)) {
					stackOfStates.remove(state);
				}

				// representar SCC como ADD para tornar mais eficiente.
				// the next loop must be in the transposed adjacency list.
				for (ArrayList<Boolean> nextState : transposedAdjacencyList
						.get(state)) {

					if (stateExpanded.get(nextState) == null
							&& stateToSCCId.get(nextState) == null) {
						ArrayList<ArrayList<Boolean>> metaState = SCCIdToMetaStates
								.get(numberOfComponents);
						metaState.add(nextState);
						SCCIdToMetaStates.put(numberOfComponents, metaState);
						stateToSCCId.put(nextState, numberOfComponents);
						stateExpanded.put(nextState, true);
						territory.push(nextState);
						componentDD = DDUtils.UpdateValue(_context,
								componentDD, nextState, numberOfComponents + 1);
						ArrayList<ArrayList<Boolean>> statesInCurrentComponent = statesByTopologicalOrder
								.get(numberOfComponents + 1);
						if (statesInCurrentComponent == null) {
							statesInCurrentComponent = new ArrayList<ArrayList<Boolean>>();
						}
						ArrayList<Boolean> nextStateClone = (ArrayList<Boolean>) nextState
								.clone();
						// nextStateClone.add(0, null);
						statesInCurrentComponent.add(nextStateClone);
						statesByTopologicalOrder.put(numberOfComponents + 1,
								statesInCurrentComponent);
						// _context.getGraph(componentDD).launchViewer();
					}

					if (stackOfStates.contains(nextState)) {
						stackOfStates.remove(nextState);
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

	/**
	 * TVI Algorithm.
	 */
	public void doTopologicalValueIteration(
			ArrayList<Boolean> currentAbstractState, double bellmanError,
			int horizon,
			HashMap<Integer, Integer> stronglyConnectedComponentsDDs)
			throws TimeLimitExceededException {
		new ArrayList<ArrayList<Boolean>>();
		currentAbstractState.clone();

		ArrayList<ArrayList<Boolean>> mdpAbstractStates = new ArrayList<ArrayList<Boolean>>();

		for (Integer componentId : stronglyConnectedComponentsDDs.keySet()) {
			ArrayList<ArrayList<Boolean>> states = statesByTopologicalOrder
					.get(componentId);
			mdpAbstractStates.addAll(states);
		}

		for (ArrayList<Boolean> abstractState : mdpAbstractStates) {
			valueFunction.put(abstractState, 0.0d);
			previousValueFunction.put(abstractState, 0.0d);
		}

		for (Integer currentComponent = stronglyConnectedComponentsDDs.size(); currentComponent > 0.0d; currentComponent--) {
			// does not work sometimes
			mdpAbstractStates = statesByTopologicalOrder.get(currentComponent);
			while (true) {
				double currentBellmanError = 0;

				for (ArrayList<Boolean> abstractState : mdpAbstractStates) {
					abstractState = updateStateVI(abstractState);
					double residual = Math.abs(valueFunction.get(abstractState)
							- previousValueFunction.get(abstractState));
					currentBellmanError = Math.max(currentBellmanError,
							residual);
				}

				if (currentBellmanError < maximumBellmanError) {
					break;
				}

			}
		}
	}

	/**
	 * Method to find valid assignments in an abstract state.
	 */
	public void findValidAssignments(ArrayList<Boolean> currentAssignment,
			HashSet<ArrayList<Boolean>> validAssignments, int i) {
		if (i == -1) {
			validAssignments.add(currentAssignment);
		} else {
			ArrayList<Boolean> currentAssignmentTrue = (ArrayList<Boolean>) currentAssignment
					.clone();
			if (currentAssignmentTrue.get(i) == null) {
				currentAssignmentTrue.set(i, true);
			}

			findValidAssignments(currentAssignmentTrue, validAssignments, i - 1);

			ArrayList<Boolean> currentAssignmentFalse = (ArrayList<Boolean>) currentAssignment
					.clone();

			if (currentAssignmentFalse.get(i) == null) {
				currentAssignmentFalse.set(i, false);
			}

			findValidAssignments(currentAssignmentFalse, validAssignments,
					i - 1);
		}
	}

	/**
	 * Method to verify if an action is ready to be used in a given state.
	 */
	public boolean acaoDisponivel(ArrayList<Boolean> currentState, Action a) {
		boolean aplicavel = false;
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get
		// (currentState);
		ArrayList<ActionTransition> acoesDisponiveis = enabledActions
				.get(currentState);

		if (acoesDisponiveis != null) {
			for (int i = 0; i < acoesDisponiveis.size(); i++) {
				ActionTransition at = acoesDisponiveis.get(i);
				if (at.getAction()._csActionName.equals(a._csActionName)) {
					aplicavel = true;
					return aplicavel;
				}
			}
		}
		return aplicavel;
	}


	/**
	 * Method to get an action and their transition probabilities given a pair (s,a).
	 */
	public ActionTransition getAcao(ArrayList<Boolean> currentState, Action a) {
		ArrayList<ActionTransition> acoesDisponiveis = enabledActions
				.get(currentState);

		if (acoesDisponiveis != null) {
			for (int i = 0; i < acoesDisponiveis.size(); i++) {
				ActionTransition at = acoesDisponiveis.get(i);
				if (at.getAction()._csActionName.equals(a._csActionName)) {
					return at;
				}
			}
		}
		return null;
	}

	/**
	 * Method that gets the greedy action given a current state.
	 */
	public ActionTransition getGreedyAction(ArrayList<Boolean> state) {
		double gamma = _dDiscount;

		ActionTransition acaoOtima = null;
		double qOtimo = -Float.MAX_VALUE;
		Double q = -Double.MAX_VALUE;

		// find best action
		for (CString a : _hmActionName2Action.keySet()) {
			Action action = _hmActionName2Action.get(a);
			ActionTransition acao = new ActionTransition(action,
					new ArrayList<ProbState>());
			if (!acaoDisponivel(state, action)) {
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));

				double recompensa = _context.evaluate(action._reward, atribb);
				// _context.getGraph(action._reward).launchViewer();

				acao.setReward(recompensa);

				ArrayList<ProbState> transicoes = computeSuccessorsProbEnum(
						atribb, action._hmVarID2CPT, action._csActionName, true);
				acao.setTransitions(transicoes);
				ArrayList<ActionTransition> acoesDisponiveis = enabledActions
						.get(state);
				if (acoesDisponiveis == null) {
					acoesDisponiveis = new ArrayList<ActionTransition>();
				}
				acoesDisponiveis.add(acao);
				enabledActions.put(state, acoesDisponiveis);
			} else {
				acao = getAcao(state, action);
			}

			ArrayList<ProbState> transicoes = acao.getTransitions();
			double somatorio = 0.0d;

			for (int j = 0; j < transicoes.size(); j++) {
				ProbState transicao = transicoes.get(j);
				double probabilidade = transicao._dProb;
				double valor = valueFunction.get(transicao.nextRepresentant);
				somatorio += probabilidade * valor;
			}

			q = acao.getReward() + gamma * somatorio;
			acao.setQValue(q);

			if (q > qOtimo) {
				acaoOtima = acao;
				qOtimo = q;
			}
		}
		return acaoOtima;
	}

	/**
	 * Method that updates a state value considering the algorithm VI.
	 */
	public ArrayList<Boolean> updateStateVI(ArrayList<Boolean> state) {
		ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = getGreedyAction(state);
		pi.put(stateClone, acaoOtima);
		previousValueFunction.put(stateClone, valueFunction.get(stateClone));
		valueFunction.put(stateClone, acaoOtima.getQValue());
		return state;
	}

	/**
	 * Method that gets a block value given its assignment of variables.
	 */
	public double getValorBloco(ArrayList<Boolean> assign) {
		if (assign != null) {
			assign.remove(0);
			double valorBloco = _context.evaluate(stochasticBisimulation,
					assign);
			assign.add(0, null);
			return valorBloco;
		} else {
			return -1;
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

		String OS = System.getProperty("os.name").toLowerCase();
		if (OS.indexOf("win") >= 0) {
			SEPARATOR = new String("\\");
		}

		if (OS.indexOf("nix") >= 0 || OS.indexOf("nux") >= 0
				|| OS.indexOf("aix") >= 0) {
			System.out.println("OS = Unix");
			SEPARATOR = new String("/");
		}

		System.out
				.println("\n*********************************************************");
		System.out.println(">>> ROUND INIT " + round_number + "/"
				+ total_rounds + "; time remaining = " + time_left
				+ ", horizon = " + horizon);
		System.out
				.println("*********************************************************");

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

				heuristicaAdmissivel = value_range;

				// System.out.println("Heuristica admiss�vel: "
				// + heuristicaAdmissivel);
				// System.exit(0);
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
					// System.out.println(">>> MDP in" +
					// "stantiated.");
				}
			}
		}
	}

	/**
	 * Modify to don't use ArrayList <ProbState>
	 * 
	 * @param state
	 * @param iD2ADD
	 * @param _csActionName
	 * @return
	 */
	public ArrayList<ProbState> computeSuccessorsProbEnum(
			ArrayList<Boolean> state, HashMap<Integer, Integer> iD2ADD,
			CString _csActionName, boolean extracting) {
		Integer multCPTs = _context.getConstantNode(1d);
		Integer xiprime;

		ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state.clone();

		// System.out.println("Atribb: " + state);
		int size = stateClone.size() / 2;
		for (int i = 0; i < size; i++) {
			if (stateClone.get(i) == null) {
				stateClone.set(i, false);
			}
		}
		// stateClone.remove(0);
		// System.out.println("Atribb (modified): " + state);

		for (CString x : _alStateVars) {
			xiprime = (Integer) _context._hmVarName2ID
					.get(_translation._hmPrimeRemap.get(x._string));
			Integer cpt_a_xiprime = iD2ADD.get(xiprime);
			double probTrue, probFalse;
			int levelprime = (Integer) _context._hmGVarToLevel.get(xiprime);
			stateClone.set(levelprime, true);
			probTrue = _context.evaluate(cpt_a_xiprime, stateClone);
			stateClone.set(levelprime, null);
			// state.set(levelprime, false);
			probFalse = 1 - probTrue;
			Integer Fh = _context.getConstantNode(probTrue);
			Integer Fl = _context.getConstantNode(probFalse);
			Integer newCPT = _context.getINode(xiprime, Fl, Fh, true);
			multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
		}

		// ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		ArrayList<ProbState> transicoes = new ArrayList<ProbState>();

		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		for (int i = 0; i <= _context._alOrder.size(); i++) {
			assign.add(null);
		}

		// _context.getGraph(multCPTs).launchViewer();

		customizedCPTInOrderSearch(_context.getNode(multCPTs), assign,
				transicoes, extracting);

		return transicoes;
	}

	/**
	 * Method used to discover the probabilities transitions to a next state.
	 * @param node
	 * @param assign
	 * @param transicoes
	 * @param extracting
	 */
	public void customizedCPTInOrderSearch(ADDNode node,
			ArrayList<Boolean> assign, ArrayList<ProbState> transicoes,
			boolean extracting) {
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);
				int id_var_prime = _hmPrimeVarID2VarID
						.get(internalNode._nTestVarID);
				int level_var = (Integer) _context._hmGVarToLevel
						.get(id_var_prime);

				// Expande a subarvore low
				ArrayList<Boolean> assignFalse = (ArrayList<Boolean>) assign
						.clone();
				assignFalse.set(level_var, new Boolean(false));
				customizedCPTInOrderSearch(lowNode, assignFalse, transicoes,
						extracting);

				// Expande a subarvore high
				ArrayList<Boolean> assignTrue = (ArrayList<Boolean>) assign
						.clone();
				assignTrue.set(level_var, new Boolean(true));
				customizedCPTInOrderSearch(highNode, assignTrue, transicoes,
						extracting);

			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de
				// serem alcançados
				if (probabilidade > 0.0d) {

					@SuppressWarnings("unchecked")
					ArrayList<Boolean> newAssign = (ArrayList<Boolean>) assign
							.clone();
					boolean hasNulls = false;

					for (int i = 0; i < newAssign.size() / 2; i++) {
						if (newAssign.get(i) == null) {
							newAssign.set(i, false);
							hasNulls = true;
						}
					}

					double valorBloco = _context.evaluate(
							stochasticBisimulation, newAssign);
					newAssign.add(0, null);

					ArrayList<Boolean> representantAux = mdp
							.getRepresentant(valorBloco);

					if (representantAux != null) {
						// Transi��o para um estado que j� foi adicionado ao
						// MDP.
						boolean transitionExists = false;
						for (int i = 0; i < transicoes.size(); i++) {
							ProbState t = transicoes.get(i);
							double valorBlocoAlState = getValorBloco(t.nextRepresentant);
							ArrayList<Boolean> alStateRepresentant = mdp
									.setRepresentant(valorBlocoAlState,
											t.nextRepresentant);

							if (alStateRepresentant.equals(representantAux)) {
								t._dProb = t._dProb
										+ probabilidade.floatValue();
								transitionExists = true;
								break;
							}
						}

						if (!transitionExists) {
							ProbState t = new ProbState(probabilidade,
									representantAux);
							transicoes.add(t);
						}

						if (valueFunction.get(representantAux) == null) {
							valueFunction.put(representantAux,
									heuristicaAdmissivel);
							solved.put(representantAux, false);
						}
					} else {
						// Estado seguinte que ainda n�o est� no MDP.
						if (extracting) {
							HashSet blocos = new HashSet();
							_context.collectLeaves(stochasticBisimulation,
									blocos);

							ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) newAssign
									.clone();
							stateAssignClone.remove(0);
							if (!hasNulls) {
								valorBloco = _context.evaluate(
										stochasticBisimulation,
										stateAssignClone);
								stateAssignClone.add(0, null);
								ArrayList<Boolean> representant = mdp
										.setRepresentant(valorBloco,
												stateAssignClone);
								ProbState t = new ProbState(probabilidade,
										representant);
								transicoes.add(t);

								if (valueFunction.get(representant) == null) {
									valueFunction.put(representant,
											heuristicaAdmissivel);
									solved.put(representant, false);
								}
							} else {
								stateAssignClone.add(0, null);
								HashSet<ArrayList<Boolean>> validAssignments = new HashSet<ArrayList<Boolean>>();
								findValidAssignments(assign, validAssignments,
										(assign.size() / 2) - 1);
								for (ArrayList<Boolean> assignment : validAssignments) {
									ProbState t = null;
									valorBloco = _context.evaluate(
											stochasticBisimulation, assignment);
									assignment.add(0, null);

									ArrayList<Boolean> representant = mdp
											.setRepresentant(valorBloco,
													assignment);
									boolean transitionExists = false;
									for (int i = 0; i < transicoes.size(); i++) {
										t = transicoes.get(i);
										double valorBlocoAlState = getValorBloco(t.nextRepresentant);
										ArrayList<Boolean> alStateRepresentant = mdp
												.setRepresentant(
														valorBlocoAlState,
														t.nextRepresentant);
										if (alStateRepresentant
												.equals(representant)) {
											t._dProb = t._dProb + probabilidade;
											transitionExists = true;
											break;
										}
									}

									if (!transitionExists) {
										t = new ProbState(probabilidade,
												representant);
										transicoes.add(t);
									}

									if (valueFunction.get(representant) == null) {
										valueFunction.put(representant,
												heuristicaAdmissivel);
										solved.put(representant, false);
									}
								}
							}

						}
					}
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
				stochasticBisimulationTime, lrtdpTime, reward, valueFunctionS0,
				"ReachMRFSWithTopologicalValueIteration");
		// clearEverything();
	}

	public void clearEverything() {
		// TODO Auto-generated method stub
		_context.clearSpecialNodes();	
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

	public void checkTimeLimit() throws TimeOutException {
		double elapsed_time = (System.currentTimeMillis() - _lStartTime) / 1000d;
		if (elapsed_time > (double) _nTimeLimitSecs)
			throw new TimeOutException("Elapsed time " + elapsed_time
					+ " (s) exceeded time limit of " + _nTimeLimitSecs + " (s)");
	}

	public static String MemDisplay() {
		long total = RUNTIME.totalMemory() / (1024 * 1024);
		long free = RUNTIME.freeMemory() / (1024 * 1024);
		return "Used Memory: " + (total - free) + " MB / Total Memory: "
				+ total + " MB ";
	}

	public void setLimitTime(Integer time) {
		AGGREGATION_TIME_LIMIT = time;
	}
}