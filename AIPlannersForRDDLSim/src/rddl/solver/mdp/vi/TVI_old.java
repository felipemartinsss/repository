/**
 * RDDL: Stochastic bissimulaation implementation.
 * 
 * @author Felipe Martins dos Santos (felipemartinsss [at] gmail.com)
 *
 * This is a Java version of factored stochastic bissimulation for model reduction:
 * 
 *   R. Givan, T. Dean and M. Greig
 *   Equivalence Notions and Model Minimization in Markov Decision Processes 
 *   Journal of Artificial Intelligence - 2003
 *
 * Example: how to run
 *  run files\final_comp\rddl rddl.solver.mdp.sbisimulation.StochasticBisimulation sysadmin_inst_mdp_agregacao_1
 **/

package rddl.solver.mdp.vi;

import java.awt.Color;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigDecimal;
import java.text.DecimalFormat;
import java.util.*;
import java.util.concurrent.ConcurrentLinkedQueue;

import javax.naming.TimeLimitExceededException;
import util.Estado;
import util.MDP;
import util.Politica;
import dd.discrete.ADDBNode;
import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;
import dd.discrete.ADD;
import dd.discrete.DD;
import rddl.*;
import rddl.RDDL.*;
import rddl.policy.Policy;
import rddl.policy.SPerseusSPUDDPolicy;
import rddl.solver.DDUtils;
import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import rddl.solver.mdp.rtdp.RTDPEnum.ProbState;
import rddl.solver.mdp.rtdp.off_LRTDPEnum.QUpdateResult;
import rddl.solver.mdp.sbisimulation.ReachMRFSWithLRTDP.ActionTransition;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Cronometro;
import util.GeradorDeArquivo;
import util.Pair;
import util.ProblemDescription;
import util.SieveOfEratosthenes;

public class TVI_old extends Policy {
	private static boolean ONLY_REACHABILITY_ANALYSIS = false;
	private static boolean ONLY_BISIMULATION = false;
	// private static boolean DEBUG = true;
	// private static boolean INTERRUPTION = false;
	// private static boolean GENERATE_PARTITION_FILE = false;
	private static boolean MODEL_MINIMIZATION = false;
	private static boolean ONLY_USEFUL_PARTITIONS = true; // Nao pode ser true se MODEL_MINIMIZATION = true.
	private static boolean BISIMULATION_INFO = true;
	private static boolean BISIMULATION_WITH_REACHABILITY_ANALYSIS = true;
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;
	private static boolean USING_BINARY_SEARCH_SORTITION = true;
	private final static int VI = 0;
	private final static int LRTDP = 1;
	private static int PLANEJADOR = VI;

	private static int MINUTE = 60;
	private static int HOUR = 60 * MINUTE;
	private static int DAY = 24 * HOUR; 

	private static int AGGREGATION_TIME_LIMIT = 2 * DAY; // Solver time limit
	private static int OFFLINE_SOLVER_TIME_LIMIT = (int) (90 * DAY); // seconds for one OFFLINE getAction
	private static int ONLINE_SOLVER_TIME_LIMIT = 10; // seconds for one ONLINE getAction
	
	private static int OFFLINE = 0;
	private static int ONLINE = 1;
	private static int PLANEJAMENTO = OFFLINE;
	
	private static int NAO_OTIMO = 0;
	private static int OTIMO = 1;
	
	// Parï¿½metro utilizado para permitir agregaï¿½ï¿½es de estados 'aproximadamente
	// iguais => epsilon \in [0,1]
	private double EPSILON_APROXIMATION = 0.0d;	// 0.000001d;
	private double EPSILON_MODEL_REDUCTION = 0.0d; // use 0.05 for the approx_example
	
	// Parï¿½metro utilizado para verificar a convergï¿½ncia do algoritmo LRTDP.
	private double maximumBellmanError = 0.001d; // 10^(-3)
	
	private boolean IGNORE_NOOP = false;
	
	// Se for APROXIMATION_IN_REWARD = false, teremos EPSILON = 0 para a funï¿½ï¿½o recompensa.
	private boolean APROXIMATION_IN_REWARD = true;
	
	private boolean SHOW_PARTITION_DETERMINING = false;
	
	private static int partitionSize = 0;
	
	private static long maxSSplitCalls = -1;
	
	private static final double FRACAO_CHAMADAS = 1.0d;
	
	private boolean rtdpExecuted = false;
	private int getActionCounter = 0;
	private Cronometro getActionTimer;
	private HashMap<ArrayList<Boolean>, Double> allAssignmentsStochasticBisimulation = null;
	private int reachableStates = 0;
	private Cronometro reachabilityTime;
	private HashMap _hmStringPrimeVarID2VarID;
	private HashMap _hmNextVarID2VarID;
	
	private Cronometro tviTime;

	public final static boolean SHOW_STATE = true;
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
	public HashMap<CString, Action> _hmActionName2Action; // Holds transition
	LinkedList <Integer> layers;														// function

	private HashMap <Integer, Boolean> isADDRedundant = null;
	private HashMap <ArrayList <Boolean>, Double> valueFunction;
	private HashMap <ArrayList <Boolean>, Double> previousValueFunction;
	private HashMap <ArrayList <Boolean>, Boolean> solved;
	// private HashMap <ArrayList <Boolean>, Float> previousValueFunction;
	
	
	Cronometro lrtdpTime;
	boolean firstTrial = true;

	int trials = 1;
	int turn = 0; // turn = 0 => pes; turn = 1 => opt.
	
	HashMap <Integer, HashSet<Estado>> statesPerHorizon;
	HashMap <Integer, Politica> policyPerHorizon;

	LinkedList <Integer> _sOpen;
	LinkedList <ArrayList> closed;
	public int _nSolvedADD = 0;
	int _nOpenAdd;
	int _nClosedAdd;
	private int _nClosed;
	private int reachableStatesSize = 0;
	private int convergidos = 0;

	private MDP mdp = null;
	// private Politica pi = null;
	HashMap <ArrayList <Boolean>, ActionTransition> pi = null;
	Integer stochasticBisimulation = -1;
	private double maxReward = -Double.MAX_VALUE;
	private double minReward = Double.MAX_VALUE;

	private String instanceName;
	private double heuristicaAdmissivel;
	private Cronometro stochasticBisimulationTime;
	private int testesDeEstabilidadeEvitados = 0;
	private Hashtable reduceRemapLeavesCache = new Hashtable();
	private Hashtable simplifyPartitionCache = new Hashtable();
	ArrayList <Integer> primeNumbers = new ArrayList <Integer>();
	LinkedHashMap <Integer, Boolean> primeUsed = new LinkedHashMap <Integer, Boolean> ();
	private int missingPrimes = 0;
	private ProblemDescription problemDescription = null;
	private Integer rewardPartitionSize = null;
	private ArrayList <Integer> usefulPartitions = null;
	private int usefulPartitionsOriginalSize;
	SieveOfEratosthenes soe; // useful to compute the prime numbers needed to represent ADD partitions.
	HashMap <Integer, Boolean> blockStable = new HashMap <Integer, Boolean> ();
	HashMap <LinkedHashSet<Integer>, ArrayList <Integer>> fluentwisePartitionsUsed = new HashMap <LinkedHashSet<Integer>, ArrayList <Integer>>();
	ArrayList <Boolean> initialState;
	
	// Local constants
	public final static int VERBOSE_LEVEL = 1; // Determines how much output is
												// displayed

	public final static boolean ALWAYS_FLUSH = false; // Always flush DD caches?
	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush
																// until < this
																// amt

	// For printing
	public final static DecimalFormat _df = new DecimalFormat("#.###");

	// Timing variables
	public long _lStartTime; // For timing purposes
	public int _nTimeLimitSecs;
	public static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	public INSTANCE _rddlInstance = null;
	public int _valueDD;
	public int _maxDD;
	public int _prevDD;
	public int _nDDType; // Type of DD to use
	public int _nIter;
	public double _dRewardRange; // Important if approximating
	public double _dDiscount;
	public int _nHorizon;
	public CString _sRegrAction;
	public ArrayList<Integer> _alSaveNodes; // Nodes to save during cache
											// flushing
	public HashMap<CString, Integer> _hmAct2Regr; // Cached DDs from last
													// regression step

	private HashMap<Integer, Integer> _hmPrimeVarID2VarID;
	
	// Just use the default random seed
	public Random _rand = new Random();
	private boolean GET_NUMBER_OF_REACHABLE_STATES = false;

	// Constructors
	public TVI_old() {
	}

	public TVI_old(
			String instance_name) {
		super(instance_name);
	}
	
	public static class ProbState implements Comparable{
		public double  _dProb;
		public ArrayList<Boolean> nextRepresentant;
		HashMap <ArrayList<Boolean>, ArrayList<ArrayList<Boolean>>> adjacencyList = new HashMap <ArrayList<Boolean>, ArrayList<ArrayList<Boolean>>>();
		public ProbState(double Prob, ArrayList<Boolean> State) {
			_dProb = Prob;
			nextRepresentant = State;
		}
		public String toString(){
			return nextRepresentant.toString();
		} 

		public boolean equals( Object objeto ) {
			if (objeto == null || !(objeto instanceof ProbState) || !(objeto instanceof Double)) return false;
			double probaCompara = (objeto instanceof ProbState? ((ProbState)objeto)._dProb: (Double)objeto);
			return probaCompara == _dProb;
		} 

		public int hashCode() {
			return ((Double)_dProb).hashCode();
		} 

		public int compareTo( Object objeto ) {
			if (objeto == null || !(objeto instanceof ProbState) || !(objeto instanceof Double)) return -1;
			double probaCompara = (objeto instanceof ProbState? ((ProbState)objeto)._dProb: (Double)objeto);
			return ((Double)probaCompara).compareTo((Double)_dProb);
		}
	}
	
	HashMap <ArrayList<Boolean>, Boolean> discoveredStates = new HashMap <ArrayList<Boolean>, Boolean>();

	/* Visita os estados do MDP com uma estratégia de busca de profundidade e preenche e gera a lista de adjacência de estados do MDP (estados alcançáveis computados aqui) */ 
	public void depthFirstSearch (ArrayList<Boolean> state, int currentHorizon, 
			Stack <ArrayList<Boolean>> stackOfStates, HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {
		discoveredStates.put(state, true);
		adjacencyList.put(state, new HashSet <ArrayList<Boolean>>());
		
		if (applicableActions.get(state) == null) {
			HashSet <Action> actions = new HashSet <Action>(_hmActionName2Action.values());
			applicableActions.put(state, actions);
		}
		
		for (Action a : applicableActions.get(state)) {
			ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
			ArrayList <ProbState> transicoes = computeSuccesorsEnum(atribb, a._hmVarID2CPT);
			for (int i = 0; i < transicoes.size(); i++) {
				ArrayList <Boolean> nextState = transicoes.get(i).nextRepresentant;
				// adiciona nextState como um estado vizinho de state
				adjacencyList.get(state).add(nextState);
				if ((discoveredStates.get(nextState) == null || discoveredStates.get(nextState).booleanValue() == false)/* && (currentHorizon < 50)*/ ) {
					depthFirstSearch (nextState, currentHorizon + 1, stackOfStates, adjacencyList);
				}
			}
		}
		stackOfStates.push(state);
	}
	
	/* Gera uma lista de adjacência transposta a partir da lista de adjacência. Ou seja, se existe P(s'|s,a) na lista de adjacência, nas lista de adjacência tranposta 
	 * existirá P(s|s',a). */
	public HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> getTransposedAdjacencyList (HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList) {
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> transposedAdjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		for (ArrayList<Boolean> state : adjacencyList.keySet()) {
			HashSet<ArrayList<Boolean>> successors = adjacencyList.get(state);
			for (ArrayList <Boolean> eachSuccessor : successors) {
				HashSet <ArrayList<Boolean>> transposedSuccessors = transposedAdjacencyList.get(eachSuccessor);
				if (transposedSuccessors == null) {
					transposedSuccessors = new HashSet <ArrayList<Boolean>>(); 
				}
				transposedSuccessors.add(state);
				transposedAdjacencyList.put(eachSuccessor, transposedSuccessors);
			}
		}
		return transposedAdjacencyList;
	}
	
	// As duas estruturas de dados a seguir são necessárias para indicar ao Value Iteration que estados atualizar em conjunto.
	HashMap <ArrayList<Boolean>, Integer> stateToSCCId = new HashMap <ArrayList<Boolean>, Integer>(); 
	HashMap <Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap <Integer, ArrayList<ArrayList<Boolean>>>();
	
	public int kosaraju (ArrayList <Boolean> add_state_assign_clone) {
		Integer numberOfComponents = 0;
		
		HashMap <ArrayList<Boolean>, Boolean> stateExpanded = new HashMap <ArrayList<Boolean>, Boolean>(); 
		
		Stack <ArrayList<Boolean>> stackOfStates = new Stack<ArrayList<Boolean>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> adjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>> transposedAdjacencyList = new HashMap<ArrayList<Boolean>, HashSet<ArrayList<Boolean>>>();
		depthFirstSearch((ArrayList <Boolean>) add_state_assign_clone, 0, stackOfStates, adjacencyList);
		transposedAdjacencyList = getTransposedAdjacencyList(adjacencyList);
		
		while (!stackOfStates.isEmpty()) {
			Integer componentDD = _context.getConstantNode(0);
			// System.out.println("Outer Iterations = " + iterations++);
			ArrayList <Boolean> state = stackOfStates.pop();
			Stack <ArrayList<Boolean>> territory = new Stack<ArrayList<Boolean>>();
			
			// se for um estado que ainda não foi visitado.
			if (SCCIdToMetaStates.get(numberOfComponents) == null) {
				ArrayList <ArrayList<Boolean>> metaState = new ArrayList <ArrayList<Boolean>>();
				metaState.add(state);
				SCCIdToMetaStates.put(numberOfComponents, metaState);
				stateToSCCId.put(state, numberOfComponents);
				stateExpanded.put(state, true);
				territory.push(state);
				componentDD = DDUtils.UpdateValue(_context, componentDD, state, numberOfComponents + 1);
			}
			
			while (!territory.isEmpty()) {
				state = territory.pop();
				
				if (stackOfStates.contains(state)) {
					stackOfStates.remove(state);
				}
				
				// representar SCC como ADD para tornar mais eficiente.
				// the next loop must be in the transposed adjacency list.
				HashSet <ArrayList <Boolean>> listForCurrentState = transposedAdjacencyList.get(state);
				if (listForCurrentState != null) {
					for (ArrayList <Boolean> nextState : listForCurrentState) {
						
						if (stateExpanded.get(nextState) == null && stateToSCCId.get(nextState) == null) {
							ArrayList <ArrayList<Boolean>> metaState = SCCIdToMetaStates.get(numberOfComponents);
							metaState.add(nextState);
							SCCIdToMetaStates.put(numberOfComponents, metaState);
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
			stronglyConnectedComponentsDDs.put(numberOfComponents + 1, componentDD);
			//_context.getGraph(componentDD).launchViewer();
			numberOfComponents++;
		}
		return numberOfComponents;
	}
	
	
	
	HashMap <ArrayList<Boolean>, Double> lowerBounds = new HashMap <ArrayList<Boolean>, Double>();
	HashMap <ArrayList<Boolean>, Double> uppeerBounds = new HashMap <ArrayList<Boolean>, Double>();
	private int searchIterations = 100;
	private double y = 0.03;
	private double currentBellmanError;
	
	private int maximumHorizon = 40;
	
	
	HashMap<ArrayList<Boolean>, HashSet<Action>> applicableActions = new HashMap<ArrayList<Boolean>, HashSet<Action>>(); 
	
	public Double backup (ArrayList <Boolean> state) {
		Double minLowerQValue = Double.MAX_VALUE;
		Double minUpperQValue = Double.MAX_VALUE;
		for (Action a : _hmActionName2Action.values()) {
			ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
			ArrayList <ProbState> transicoes = computeSuccesorsEnum(atribb, a._hmVarID2CPT);
			Double currentActionUpperValue = 0.0d;
			Double currentActionLowerValue = 0.0d;
			for (int i = 0; i < transicoes.size(); i++) {
				ProbState probState = transicoes.get(i);
				currentActionUpperValue += probState._dProb * _context.evaluate(valueFunctionUpperBounds, state);
				currentActionLowerValue += probState._dProb * _context.evaluate(valueFunctionLowerBounds, state);
			}
			currentActionUpperValue += _context.evaluate(a._reward, state);
			currentActionLowerValue += _context.evaluate(a._reward, state);
			if (currentActionUpperValue < _context.evaluate(valueFunctionUpperBounds, state)) {
				System.out.println("Need to eliminate action '" + a._csActionName + "' in state " + state + ".");
				HashSet <Action> actionsInState = applicableActions.get(state);
				actionsInState.remove(a);
			}
			
			if (currentActionLowerValue < minLowerQValue) {
				minLowerQValue = currentActionLowerValue;
			}
			
			if (currentActionUpperValue < minUpperQValue) {
				minUpperQValue = currentActionUpperValue;
			}
			
			
		}
		Double oldValue = _context.evaluate(valueFunctionLowerBounds, state);
		valueFunctionLowerBounds = DDUtils.UpdateValue(_context, valueFunctionLowerBounds, state, minLowerQValue);
		valueFunctionUpperBounds = DDUtils.UpdateValue(_context, valueFunctionUpperBounds, state, minUpperQValue);
		return Math.abs(minLowerQValue - oldValue);
	}
	
	
	
	int visitedStatesInFTVI;
public void focusedTopologicalVI (ArrayList <Boolean> initialState) {
		
		
		
		Double upperAdmissibleHeuristic = -Double.MAX_VALUE;
		Double lowerAdmissibleHeuristic = Double.MAX_VALUE;
		
		for (Action a : _hmActionName2Action.values()) {
			upperAdmissibleHeuristic = Math.max(upperAdmissibleHeuristic, _context.getMaxValue(a._reward));
			lowerAdmissibleHeuristic = Math.min(lowerAdmissibleHeuristic, _context.getMinValue(a._reward));
		}
		
		if (_dDiscount < 1d) {
			upperAdmissibleHeuristic = upperAdmissibleHeuristic / (1d - _dDiscount);
			lowerAdmissibleHeuristic = lowerAdmissibleHeuristic / (1d - _dDiscount);
		} else {
			upperAdmissibleHeuristic = upperAdmissibleHeuristic * _nHorizon;
			lowerAdmissibleHeuristic = lowerAdmissibleHeuristic * _nHorizon;
		}
		
		valueFunctionLowerBounds = _context.getConstantNode(lowerAdmissibleHeuristic);
		valueFunctionUpperBounds = _context.getConstantNode(upperAdmissibleHeuristic);
		
		optimalPolicy = new HashMap <ArrayList <Boolean>, String> ();
		
		while (true) {
			double oldValue = _context.evaluate(valueFunctionLowerBounds, initialState);
			for (int i = 0; i < searchIterations; i++) {
				System.out.println("Search iterations FTVI: " + i);
				currentBellmanError = 0.0d;
				
				visitedStatesInFTVI = _context.getConstantNode(0);
				
				ArrayList <Boolean> state = (ArrayList<Boolean>) initialState.clone();
				currentBellmanError = search (state, 0, currentBellmanError);
				if (currentBellmanError <  maximumBellmanError) {
					return;
				}
			}
			
			Double currentValue = _context.evaluate(valueFunctionUpperBounds, initialState);
			Double fractionOfDifference = currentValue / oldValue;
			assert (fractionOfDifference <= 1.0d);
			if (fractionOfDifference > (1.0d - y)) {
			 	break;
			}
		}
	}
	
	int valueFunctionLowerBounds;
	int valueFunctionUpperBounds;
	public Double search (ArrayList <Boolean> state, Integer horizon, Double currentBellmanError) {
		if (horizon <= maximumHorizon) {
			visitedStatesInFTVI = DDUtils.UpdateValue(_context, visitedStatesInFTVI, state, 1);
			Action a = computeGreedyAction (state);
			ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
			ArrayList <ProbState> transicoes = computeSuccesorsEnum(atribb, a._hmVarID2CPT);
			Double currentActionValue = 0.0d;
			for (int i = 0; i < transicoes.size(); i++) {
				ProbState transicao = transicoes.get(i);
				ArrayList <Boolean> successor = transicao.nextRepresentant;
				if (_context.evaluate(visitedStatesInFTVI, successor) == 0.0d) {
					currentBellmanError = search (successor, horizon + 1, currentBellmanError);
				}
			}
			currentBellmanError = Math.max (currentBellmanError, backup(state));
		}
		return currentBellmanError;
	}
	
	HashMap <ArrayList <Boolean>, Boolean> stateVisited = new HashMap <ArrayList <Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, String> optimalPolicy = new HashMap<ArrayList<Boolean>, String>(); 
	
	public Action computeGreedyAction (ArrayList <Boolean> state) {
		Action greedyAction = null;
		Double greedyActionValue = -Double.MAX_VALUE;
		HashMap <Action, Double> qValues = new HashMap <Action, Double> ();
		for (Action a : _hmActionName2Action.values()) {
			
			if (applicableActions.get(state) == null) {
				HashSet <Action> actions = new HashSet <Action>();
				actions.add(a);
				applicableActions.put(state, actions);
			} else {
				if ((stateVisited.get(state) == null) || (stateVisited.get(state).booleanValue() != true)) {
					HashSet <Action> actions = applicableActions.get(state);
					actions.add(a);
					applicableActions.put(state, actions);
				}
			}
			
			ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
			ArrayList <ProbState> transicoes = computeSuccesorsEnum(atribb, a._hmVarID2CPT);
			Double currentActionValue = 0.0d;
			for (int i = 0; i < transicoes.size(); i++) {
				ProbState probState = transicoes.get(i);
				currentActionValue += probState._dProb * _context.evaluate(valueFunctionUpperBounds, probState.nextRepresentant);
			}
			currentActionValue = _context.evaluate(a._reward, state) + _dDiscount * currentActionValue;
			qValues.put(a, currentActionValue);
			
			if (greedyAction == null) {
				greedyAction = a;
				greedyActionValue = qValues.get(a);
			} else {
				if (greedyActionValue < currentActionValue) {
					greedyAction = a;
					greedyActionValue = currentActionValue;
				}
			}
			
			
			currentActionValue = null;
		}
		optimalPolicy.put(state, greedyAction._csActionName.toString());
		stateVisited.put(state, true);
		return greedyAction;
	}
	
	HashMap <Integer, Integer> stronglyConnectedComponentsDDs = new HashMap <Integer, Integer> ();

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
			previousValueFunction = new HashMap <ArrayList <Boolean>, Double> ();
			valueFunction = new HashMap <ArrayList <Boolean>, Double> ();
			solved = new HashMap <ArrayList <Boolean>, Boolean>();
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
		ArrayList add_state_assign = DDUtils.ConvertTrueVars2DDAssign(_context, true_vars, _alStateVars);
		ArrayList<Boolean> stateAssign = (ArrayList<Boolean>) add_state_assign;
		stateAssign.add(0, null);
		
		ArrayList <Boolean> add_state_assign_clone = (ArrayList <Boolean>) add_state_assign.clone();
		add_state_assign_clone.remove(0);
		
		
		// compute the Reachability-based model minimization
		if (getActionCounter == 0) {
			stochasticBisimulationTime = new Cronometro();
			reachabilityTime = new Cronometro();
			
			// Focused Topological Value Iteration (optional - uncomment it to use it)
			// focusedTopologicalVI(add_state_assign_clone);
			
			tviTime.setStart();
			int numberOfComponents = kosaraju (add_state_assign_clone);
			
			// reachableStates = _context.getConstantNode(0);
			// for (int i = 1; i <= numberOfComponents; i++) {
			//	reachableStates = _context.applyInt(reachableStates, stronglyConnectedComponentsDDs.get(i), ADD.ARITH_SUM);
			// }
			// reachableStates = reduceRemapLeaves (reachableStates);
			// _context.getGraph(reachableStates).launchViewer();
			
			/*
			try {
				stochasticBisimulation = getReducedExplicitMDP(AGGREGATION_TIME_LIMIT);
				_context.getGraph(stochasticBisimulation).launchViewer();
			} catch (TimeOutException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			*/
			
			
			
			// Topological Value Iteration
			
			// topologicalvalueIteration (add_state_assign_clone, numberOfComponents, stateToSCCId, SCCIdToMetaStates);
			
			
			
			
				
		}
			
			
		ArrayList <Boolean> currentAbstractState = mdp.getRepresentant (stateAssign);

		if (currentAbstractState == null) {
			HashSet <ADDDNode> blocos = new HashSet <ADDDNode> ();
			_context.collectLeaves(stochasticBisimulation, blocos);
			ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) stateAssign.clone();
			stateAssignClone.remove(0);
			double valorBloco = _context.evaluate(stochasticBisimulation, stateAssignClone);
			stateAssignClone.add(0, null);
			currentAbstractState = mdp.setRepresentant(valorBloco, stateAssignClone);
				
			if (getActionCounter == 0) {
				// allAssignmentsStochasticBisimulation = getAllPaths(stochasticBisimulation, false);
				// System.out.println("Get All Paths executada para " +  _context._hmID2VarName.size() / 2 + " variaveis.");
				HashSet blocosBissimulacao = new HashSet ();
				_context.collectLeaves(stochasticBisimulation, blocosBissimulacao);
				System.out.println("Nï¿½mero de blocos da bissimulaï¿½ï¿½o estocï¿½stica: " + blocosBissimulacao.size());
				STOCHASTIC_BISIMULATION_COMPUTED = true;
				primeNumbers.clear();
				primeNumbers = null;
				soe.suggestToFreeMemory();
				flushCaches();
			}
			
			if (valueFunction.get(currentAbstractState) == null && solved.get(currentAbstractState) == null) {
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
				switch (PLANEJADOR) {
					case VI:
						try {
							if (PLANEJAMENTO == OFFLINE && getActionCounter == 0) {
								_nTimeLimitSecs = OFFLINE_SOLVER_TIME_LIMIT;
								doValueIteration(currentAbstractState, maximumBellmanError, 40, stronglyConnectedComponentsDDs);
							} else if (PLANEJAMENTO == ONLINE) {
								_nTimeLimitSecs = ONLINE_SOLVER_TIME_LIMIT;
								doValueIteration(currentAbstractState, maximumBellmanError, 40, stronglyConnectedComponentsDDs);
							}
						} catch (TimeLimitExceededException e1) {
							e1.printStackTrace();
						}
						break;
					case LRTDP:
						try {
							// pi = Resolvedor.rtdp(mdp, 0.0001f, pi);
							// Executa LRTDP atï¿½ convergir e apenas no primeiro trial.
							if (PLANEJAMENTO == OFFLINE && getActionCounter == 0) {
								_nTimeLimitSecs = OFFLINE_SOLVER_TIME_LIMIT;
								doLRTDP(currentAbstractState, maximumBellmanError, 40);
							} else if (PLANEJAMENTO == ONLINE) {
								_nTimeLimitSecs = ONLINE_SOLVER_TIME_LIMIT;
								doLRTDP(currentAbstractState, maximumBellmanError, 40);
							}
						} catch (TimeLimitExceededException e1) {
							e1.printStackTrace();
						}
						break;
					default:
						break;
				}
			}
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
			Double valorBloco = _context.evaluate(stochasticBisimulation, stateAssign);
			stateAssign.add(0, null);
			ArrayList <Boolean> representant = mdp.getRepresentant(valorBloco);
			if (representant != null) {
				ActionTransition at = pi.get(representant);
				// System.out.println("Assignments: " + e.getAtribuicoes());
				if (at != null) {
					action_taken = at.getAction()._csActionName._string;
					System.out.println("Current State: " + representant);
					System.out.println("Melhor acao: " + action_taken + " => "
							+ at.getQValue());
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
		
		/*
		try {
		 	Thread.sleep(1000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}*/

		return action_map.get(action_taken);
	}
	
	private void topologicalvalueIteration(ArrayList<Boolean> add_state_assign_clone, int numberOfComponents,
			HashMap<ArrayList<Boolean>, Integer> stateToSCCId, HashMap<Integer, ArrayList<ArrayList<Boolean>>> sCCIdToMetaStates) {
		valueFunctionVI = _context.getConstantNode(0);
		for (int i = numberOfComponents - 1; i >= 0; i--) {
			ArrayList <ArrayList <Boolean>> statesInCurrentComponent = sCCIdToMetaStates.get(new Integer(i));
			valueIteration (statesInCurrentComponent);
		}
		
	}

	int oldValueFunctionVI;
	int valueFunctionVI;
	private void valueIteration(
			ArrayList<ArrayList<Boolean>> statesInCurrentComponent) {
		
		while (true) {
			oldValueFunctionVI = valueFunctionVI;
			for (ArrayList <Boolean> state : statesInCurrentComponent) {
				HashMap <Action, Double> qValues = new HashMap <Action, Double> ();
				Double bestQValue = -Double.MAX_VALUE;
				for (Action a : _hmActionName2Action.values()) {
					ArrayList <Boolean> atribb = (ArrayList<Boolean>) state.clone();
					ArrayList <ProbState> transicoes = computeSuccesorsEnum(atribb, a._hmVarID2CPT);
					Double currentActionValue = 0.0d;
					for (int i = 0; i < transicoes.size(); i++) {
						ProbState probState = transicoes.get(i);
						currentActionValue += probState._dProb * _context.evaluate(valueFunctionVI, probState.nextRepresentant);
					}
					currentActionValue = _context.evaluate(a._reward, state) + _dDiscount * currentActionValue;
					qValues.put(a, currentActionValue);
					if (bestQValue < currentActionValue) {
						bestQValue = currentActionValue;
						optimalPolicy.put(state, a._csActionName.toString());
					}
				}
				valueFunctionVI = DDUtils.UpdateValue(_context, valueFunctionVI, state, bestQValue);
			}
			
			int valueFunctionDifference = _context.applyInt(valueFunctionVI, oldValueFunctionVI, ADD.ARITH_MINUS);
			double max_pos_diff = _context.getMaxValue(valueFunctionDifference);
			double max_neg_diff = _context.getMinValue(valueFunctionDifference);
			double max_diff = Math.max(Math.abs(max_pos_diff), Math.abs(max_neg_diff));
			if (max_diff < maximumBellmanError) {
				return;
			}
		}
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
	
	/*
	private void VI(int numberOfComponents) {
		QUpdateResult result = new QUpdateResult(null, -Double.MAX_VALUE, new ArrayList<ProbState>());
		for (int i = 1; i < numberOfComponents; i++) {
			
			ArrayList <ArrayList<Boolean>> metaState = SCCIdToMetaStates.get(i);
			for (int j = 0; j < metaState.size(); j++) {
				ArrayList <Boolean> state = metaState.get(j);
				ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
				stateClone.add(0, null);
				// updateState(stateClone);
			}
		}
	}
	*/
	Integer multCPTs = -1;
	Integer succss = -1;
	private int getImageSet (Action a, int currentReachableSet) {		
		multCPTs = currentReachableSet; 
		Integer xiprime, xi;
		// _context.getGraph(multCPTs).launchViewer();
		// System.out.print("\t\t");
		for (CString x : _alStateVars) {
			// System.out.print(x._string + " ");
			xiprime = (Integer) _context._hmVarName2ID.get(_translation._hmPrimeRemap.get(x._string));
			xi = (Integer) _context._hmVarName2ID.get(x._string);
			// Integer cpt_a_xiprime = a._hmVarID2CPT.get(xiprime);		
			reduceRemapLeavesCache = new Hashtable();
			succss = reduceRemapLeaves(a._hmVarID2CPT.get(xiprime));
			multCPTs = _context.applyInt(multCPTs, succss, ADD.ARITH_PROD);
		}
		// System.out.println();
		
		// System.out.println("\t\tSimplifying the ADD...");
		for (CString x : _alStateVars) {
			xi = (Integer) _context._hmVarName2ID.get(x._string);
			multCPTs = _context.opOut(multCPTs, xi, DD.ARITH_SUM);
		}
		// _context.getGraph(multCPTs).launchViewer();
		
		// System.out.println("\t\tRemapping GIDs...");
		multCPTs = _context.remapGIDsInt (multCPTs, _hmStringPrimeVarID2VarID);
		// _context.getGraph(multCPTs).launchViewer();
		return multCPTs;
	}
	
	// 
	public int getReachableStatesSize (int reachableStatesDD) {
		int currentHorizon = 0;
			HashMap <ArrayList <Boolean>, Integer> stateHorizon = new HashMap <ArrayList <Boolean>, Integer> ();
			ArrayList <ArrayList<Boolean>> completeStates = new ArrayList <ArrayList <Boolean>> ();
			HashMap<ArrayList<Boolean>, Double> allPaths = getAllPaths(reachableStatesDD, true);
			for (ArrayList <Boolean> assignment : allPaths.keySet()) {
				Double value = allPaths.get(assignment);
				if (value > 0.0d) {
					assignment.remove(0);
					int originalSize = assignment.size();
					for (int i = 0; i <= originalSize; i++) {
						assignment.add(null);
					}
					
					ArrayList <ArrayList<Boolean>> statesInAssignment = new ArrayList <ArrayList<Boolean>>();
					statesInAssignment.add(assignment);
					while (!statesInAssignment.isEmpty()) {
						boolean complete = true;
						assignment = statesInAssignment.remove(0);
						for (int i = 0; i < originalSize; i++) {
							if (assignment.get(i) == null) {
								complete = false;
								ArrayList <Boolean> assignmentTrue = (ArrayList<Boolean>) assignment.clone();
								ArrayList <Boolean> assignmentFalse = (ArrayList<Boolean>) assignment.clone();
								assignmentTrue.set(i, true);
								assignmentFalse.set(i, false);
								statesInAssignment.add(assignmentTrue);
								statesInAssignment.add(assignmentFalse);
								break;
							}
						}
						
						if (complete) {
							completeStates.add(assignment);
						}
					}
					
					for (ArrayList <Boolean> completeState : completeStates) {
						if (!stateHorizon.containsKey(completeState)) {
							stateHorizon.put(completeState, currentHorizon + 1);
						}
					}
				}
			}
			
			HashSet statesWithoutRepetition = new HashSet();
			statesWithoutRepetition.addAll(completeStates);
			reachableStatesSize = statesWithoutRepetition.size();
			return reachableStatesSize;
	}
	
	
	int currentLayer = -1;
	private int findReachableStates(ArrayList<Boolean> add_state_assign_clone, int horizon) {
		boolean debug = false;
		reachableStates = _context.getConstantNode(0);
		reachableStates = DDUtils.UpdateValue(_context, reachableStates, add_state_assign_clone, 1);
		currentLayer = DDUtils.UpdateValue(_context, reachableStates, add_state_assign_clone, 1);
		// _context.getGraph(reachableStates).launchViewer();
		System.out.println("Computing the reachable states set...");
		for (int i = 0; i < 40; i++) {
			// flushCaches();
			// if (debug) {
			System.out.println("h = " + i + " => |ReachableStates|");
			// }
			int nextLayer = -1;
 			for (Action a : _hmActionName2Action.values()) {
 				// System.out.println("\taction = " + a._csActionName._string);
 				
 				if (nextLayer == -1) {
 					// statesToIgnore = _context.applyInt(reachableStates, currentLayer, ADD.ARITH_MINUS);
 					nextLayer = getImageSet (a, currentLayer);
 				} else {
 					int nextLayerForCurrentAction = getImageSet (a, currentLayer);
 					// nextLayer = _context.applyInt(_context.applyInt(nextLayer, nextLayerForCurrentAction, ADD.ARITH_SUM),
 					// 							  _context.applyInt(nextLayer, nextLayerForCurrentAction, ADD.ARITH_PROD),
 					// 							  ADD.ARITH_MINUS);
 					nextLayer = _context.applyInt(nextLayer, nextLayerForCurrentAction, ADD.ARITH_SUM);
 					reduceRemapLeavesCache = new Hashtable();
 					nextLayer = reduceRemapLeaves(nextLayer);
 				}
 				// System.out.println("\t\tAdding the next layer for reachable sets...");
				// reachableStates = _context.applyInt (_context.applyInt(nextLayer, reachableStates, ADD.ARITH_SUM), _context.applyInt(nextLayer, reachableStates, ADD.ARITH_PROD), ADD.ARITH_MINUS);
				
			}
 			reachableStates = _context.applyInt(reachableStates, nextLayer, ADD.ARITH_SUM);
			reduceRemapLeavesCache = new Hashtable();
			reachableStates = reduceRemapLeaves(reachableStates);
			// _context.getGraph(currentLayer).launchViewer();
			// _context.getGraph(nextLayer).launchViewer();
			// _context.getGraph(reachableStates).launchViewer();
 			if (nextLayer == currentLayer) {
 				System.out.println("All reachable states found.");
 				break;
 			} 
 			
 			if (_context.getMax(currentLayer) == _context.getMin(currentLayer)) {
 				if (_context.getMax(currentLayer) == 1.0d) {
 					System.out.println("All states are reachable.");
 					break;
 				}
 			}
 			
 			/* else {
 				layers.offer(nextLayer);
 			} */
 			currentLayer = nextLayer;
 			flushCaches();
		}
		
		/*
		while (!layers.isEmpty()) {
			currentLayer = layers.poll();
			reachableStates = _context.applyInt(reachableStates, currentLayer, ADD.ARITH_SUM);
			reduceRemapLeavesCache = new Hashtable();
			reachableStates = reduceRemapLeaves(reachableStates);
			flushCaches();
		}
		*/
		
		// _context.getGraph(reachableStates).launchViewer();
		
		// System.out.println("Reachable States = " + getReachableStatesSize(reachableStates));
		// System.out.println("MemDisplay => " + MemDisplay());
		flushCaches();
		
		return reachableStates;
	}
	
	private static final String LOG_FILE = "ReachabilityModelReductionConvergence";
	private static final boolean ONLY_ESSENTIAL_VARS = true;
	private boolean LOG_CONVERGENCE = false;
	
	public void writeToLog(String msg) throws IOException {
		if (LOG_CONVERGENCE) {
			BufferedWriter bw = new BufferedWriter(new FileWriter(LOG_FILE + this.OS + ".log" , true));
			bw.write(msg);
			bw.newLine();
			bw.flush();
			bw.close();
		}
	}
	
	private static final int BRANCO = 0;
	private static final int CINZA = 1;
	private static final int PRETO = 2;
	LinkedHashMap <Double, ArrayList<ArrayList<Boolean>>> statesByTopologicalOrder; 
	
	ArrayList <ArrayList <Boolean>> breadthFirstSearch (ArrayList <Boolean> state, int horizon, HashMap <Integer, Integer> stronglyConnectedComponentsDDs) {
		ArrayList <ArrayList <Boolean>> mdpAbstractStates = new ArrayList <ArrayList <Boolean>>();
		HashMap <ArrayList <Boolean>, Integer> stateColorMap = new HashMap <ArrayList <Boolean>, Integer>();
		statesByTopologicalOrder = new LinkedHashMap <Double, ArrayList<ArrayList<Boolean>>>();
		mdpAbstractStates.add(state);
		stateColorMap.put(state, BRANCO);
		while (!mdpAbstractStates.isEmpty()) {
			state = mdpAbstractStates.get(0);
			if (stateColorMap.get(state) == BRANCO) {
				stateColorMap.put(state, CINZA);
				for (int i = 1; i <= stronglyConnectedComponentsDDs.size(); i++) {
					Integer component = stronglyConnectedComponentsDDs.get(i);
					ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
					stateClone.remove(0);
					Double componentId = _context.evaluate(component, stateClone);
					if (componentId != 0.0d) {
						ArrayList <ArrayList <Boolean>> statesInComponent = statesByTopologicalOrder.get (componentId);
						if (statesInComponent == null) {
							statesInComponent = new ArrayList <ArrayList <Boolean>>();
						}
						statesInComponent.add(state);
						statesByTopologicalOrder.put(componentId, statesInComponent);
						break;
					}
				}
				
				if (applicableActions.get(state) == null) {
					HashSet <Action> actions = new HashSet <Action>(_hmActionName2Action.values());
					applicableActions.put(state, actions);
				}
			
				// for (Action a : applicableActions.get(state)) {
				for (CString a : _hmActionName2Action.keySet()) {
					Action action = _hmActionName2Action.get(a);
					ActionTransition acao = new ActionTransition(action, new ArrayList <ProbState>());
					ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
					atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));
					double recompensa = _context.evaluate(action._reward, atribb);
					acao.setReward(recompensa);
					
					ArrayList <ProbState> transicoes = computeSuccessorsProbEnum(atribb, action._hmVarID2CPT, action._csActionName, true);
					for (int i = 0; i < transicoes.size(); i++) {
						ArrayList <Boolean> nextState = transicoes.get(i).nextRepresentant;
						if (stateColorMap.get(nextState) == null) {
							mdpAbstractStates.add(nextState);
							stateColorMap.put(nextState, BRANCO);
						}
					}
					
					acao.setTransitions(transicoes);
					ArrayList <ActionTransition> acoesDisponiveis = enabledActions.get(state);
					if (acoesDisponiveis == null) {
						acoesDisponiveis = new ArrayList <ActionTransition>();
					}
					acoesDisponiveis.add(acao);
					enabledActions.put(state, acoesDisponiveis);
				}
			}
						
			mdpAbstractStates.remove(state);
			stateColorMap.put(state, PRETO);
		}
		
		
		for (ArrayList <Boolean> key : stateColorMap.keySet()) {
			mdpAbstractStates.add(key);
		}
		
		return mdpAbstractStates;
	}
	
	private void doValueIteration (ArrayList <Boolean> currentAbstractState, double bellmanError, int horizon, HashMap <Integer, Integer> stronglyConnectedComponentsDDs) throws TimeLimitExceededException {
		ArrayList<ArrayList<Boolean>> estadosVisitados = new ArrayList<ArrayList<Boolean>>();
		ArrayList <Boolean> state = (ArrayList<Boolean>) currentAbstractState.clone();
		
		ArrayList <ArrayList <Boolean>> mdpAbstractStates = breadthFirstSearch (state, horizon, stronglyConnectedComponentsDDs);
		
		
		for (Double componentId : statesByTopologicalOrder.keySet()) {
			ArrayList <ArrayList <Boolean>> states = statesByTopologicalOrder.get(componentId);
			System.out.println("Component ID: " + componentId);
			System.out.println("\tStates: " + states);
		}
		
		
		for (ArrayList <Boolean> abstractState : mdpAbstractStates) {
			valueFunction.put(abstractState, 0.0d);
		}
			
		
		// Do Value Iteration for each topological component.
		for (Double currentComponent = new Double(stronglyConnectedComponentsDDs.size()); currentComponent > 0.0d; currentComponent -= 1.0d) {
			mdpAbstractStates =  statesByTopologicalOrder.get(currentComponent);
			while (true) {
				double currentBellmanError = 0;
				
				for (ArrayList <Boolean> abstractState : mdpAbstractStates) {
					abstractState = updateStateVI(abstractState);
					double residual = Math.abs(valueFunction.get(abstractState) - previousValueFunction.get(abstractState));
					currentBellmanError = Math.max(currentBellmanError, residual);
				}
				
				if (currentBellmanError < maximumBellmanError) {
					break;
				}
				
			}
		}
	}

	double valueFunctionS0;
	private void doLRTDP(ArrayList <Boolean> currentAbstractState, double bellmanError, int horizon) throws TimeLimitExceededException {
		int numberOfTrials = 0;
		lrtdpTime = new Cronometro();
		Cronometro sixtyTrialsTime = new Cronometro();
		if (PLANEJAMENTO == OFFLINE) {
			System.out.println("Stochastic Bisimulation");
			// _context.getGraph(stochasticBisimulation).launchViewer();
			lrtdpTime.setStart();
			sixtyTrialsTime.setStart();
			try {
				writeToLog(_sInstanceName);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			initialState = (ArrayList<Boolean>) currentAbstractState.clone();
			while (!solved.get(initialState)) {
				try {
					checkTimeLimit();
					initialState = (ArrayList<Boolean>) currentAbstractState.clone();
					lrtdp(initialState, bellmanError, horizon);
					// System.out.println("Residual s0 = " + mdp.obtemEstadoInicial().residual());
					// System.out.println("Convergidos = " + convergidos + "/" + partitionSize);
				} catch (TimeOutException toe) {
					System.out.println("Time limit exceeded for the getAction = "
							+ getActionCounter);
					break;
				} finally {
					numberOfTrials++;
				}
			}
			
			lrtdpTime.setEnd();
			currentAbstractState = updateState(currentAbstractState);
			valueFunctionS0 = valueFunction.get(currentAbstractState);
			try {
				writeToLog("Fim");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} 
		
		
		System.out.println("Number of trials: " + numberOfTrials);
		return;
	}

	
	public void findValidAssignments(ArrayList<Boolean> currentAssignment,
			HashSet<ArrayList<Boolean>> validAssignments, int i) {
		if (i == -1) {
			validAssignments.add(currentAssignment);
		} else {
			ArrayList<Boolean> currentAssignmentTrue = (ArrayList<Boolean>) currentAssignment.clone();
			if (currentAssignmentTrue.get(i) == null) {
				currentAssignmentTrue.set(i, true);
			}

			findValidAssignments(currentAssignmentTrue, validAssignments, i - 1);

			ArrayList<Boolean> currentAssignmentFalse = (ArrayList<Boolean>) currentAssignment.clone();

			if (currentAssignmentFalse.get(i) == null) {
				currentAssignmentFalse.set(i, false);
			}

			findValidAssignments(currentAssignmentFalse, validAssignments,
					i - 1);
		}

	}	
	
	private void lrtdp(ArrayList <Boolean> currentAbstractState, double bellmanError, int horizon) throws TimeOutException {
		
		Stack<ArrayList<Boolean>> estadosVisitados = new Stack<ArrayList<Boolean>>();
		ArrayList <Boolean> state = (ArrayList<Boolean>) currentAbstractState.clone();
		
		// System.out.println("Performing an lrtdp trial...");
		for (int i = 0; (i < horizon) && (!solved.get(state)); i++) {
			// System.out.println("steps to go = " + i);
			checkTimeLimit();
			
			estadosVisitados.push(state);
			state = updateState(state);
			
			if (state.equals(initialState)){
				double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
				try {
					writeToLog(instant + "	" + valueFunction.get(state));
					// writeToLog(state + "\t" + valueFunction.get(state));
				} catch (IOException e) {
						// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			
			state = obtemProximoEstado (state, mdp, 40);
		}

		// System.exit(0);
		
		while (!estadosVisitados.isEmpty()) {
			// checkTimeLimit();
			state = estadosVisitados.pop();
			
			if (estadosVisitados.isEmpty()) {
				state = updateState(state);
				double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
				try {
					// writeToLog("LRTDPCheckSolved for Trial: " + trials);
					writeToLog(instant + "	" + valueFunction.get(state));
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			if (!checkSolved(mdp, state, bellmanError)) {
				break;
			}
		}
		
		// System.out.println ("End of Trial: " + trials++);
	}
		
	public static class ActionTransition {
		private Action a;
		private ArrayList <ProbState> actionTransitions;
		private double reward;
		private double qValue;
		
		public ActionTransition (Action a, ArrayList <ProbState> actionTransitions) {
			this.a = a;
			this.actionTransitions = actionTransitions;
		}
		
		public Action getAction() {
			return a;
		}
		
		public ArrayList <ProbState> getTransitions() {
			return actionTransitions;
		}
		
		public void setTransitions (ArrayList <ProbState> transitions) {
			this.actionTransitions = transitions;
		}
		
		public void setReward (double reward) {
			this.reward = reward;
		}
		
		public double getReward () {
			return reward;
		}
		
		public double getQValue() {
			return qValue;
		}
		
		public void setQValue (double qValue) {
			this.qValue = qValue;
		}
		
	}
	
	HashMap <ArrayList <Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap <ArrayList <Boolean>, ArrayList<ActionTransition>>(); 
	
	public boolean acaoDisponivel (ArrayList <Boolean> currentState, Action a) {
		boolean aplicavel = false;
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get (currentState);
		ArrayList <ActionTransition> acoesDisponiveis = enabledActions.get(currentState);
		
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
	
    public ActionTransition getAcao(ArrayList <Boolean> currentState, Action a) {
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get (currentState);
		ArrayList <ActionTransition> acoesDisponiveis = enabledActions.get(currentState);
		
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
	
    public ActionTransition getGreedyAction (ArrayList <Boolean> state) {
    	double gamma = _dDiscount;
    	
		ActionTransition acaoOtima = null;
		double qOtimo = -Float.MAX_VALUE;
		Double q = -Double.MAX_VALUE;
		
		// find best action
		for (CString a : _hmActionName2Action.keySet()) {
			Action action = _hmActionName2Action.get(a);
			ActionTransition acao = new ActionTransition(action, new ArrayList <ProbState>());
			if (!acaoDisponivel(state, action)) {
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));
	
				double recompensa = _context.evaluate(action._reward, atribb);
				// _context.getGraph(action._reward).launchViewer();
	
				acao.setReward(recompensa);
	
				
				ArrayList <ProbState> transicoes = computeSuccessorsProbEnum(atribb, action._hmVarID2CPT, action._csActionName, true);
				acao.setTransitions(transicoes);
				ArrayList <ActionTransition> acoesDisponiveis = enabledActions.get(state);
				if (acoesDisponiveis == null) {
					acoesDisponiveis = new ArrayList <ActionTransition>();
				}
				acoesDisponiveis.add(acao);
				enabledActions.put(state, acoesDisponiveis);
			} else {
			 	acao = getAcao(state, action);
			}
			
			ArrayList <ProbState> transicoes = acao.getTransitions();
			double somatorio = 0.0d;
			
			for (int j = 0; j < transicoes.size(); j++) {
				if (j == 0) {
					ProbState transicao = transicoes.get(j);
					double probabilidade = transicao._dProb;
					double valor = valueFunction.get(transicao.nextRepresentant);
					somatorio += probabilidade * valor;
				} else {
					ProbState transicao = transicoes.get(j);
					double probabilidade = (transicao._dProb - transicoes.get(j - 1)._dProb);
					double valor = valueFunction.get(transicao.nextRepresentant);
					somatorio += probabilidade * valor;
				}
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
    
    public ArrayList <Boolean> updateStateVI(ArrayList <Boolean> state) {
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = getGreedyAction (state);
		pi.put(stateClone, acaoOtima);
		previousValueFunction.put(stateClone, valueFunction.get(stateClone));
		valueFunction.put(stateClone, acaoOtima.getQValue());
		return state;
	}
    
	public ArrayList <Boolean> updateState(ArrayList <Boolean> state) {
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = getGreedyAction (state);
		pi.put(stateClone, acaoOtima);
		valueFunction.put(stateClone, acaoOtima.getQValue());
		return state;
	}
	
	public ArrayList <Boolean> obtemProximoEstado (ArrayList <Boolean> estado, MDP mdp, int horizon) {
        Random rand = new Random((new Date()).getTime());
        ActionTransition acao = null;
        ArrayList <Boolean> e = null;
        double probabilidadeSorteada = 0.0d;
        int i = 0;
        
        if (PLANEJADOR == LRTDP) {
        	acao = pi.get(estado);
        }
        
        if (acao != null) {
        	ProbState t = null;
        	
        	if (USING_BINARY_SEARCH_SORTITION) {
        		ArrayList <ProbState> transicoes = acao.getTransitions();
        		int indiceInicio = 0;
        		int indiceFim = transicoes.size() - 1;
        		int indiceMeio;
        		do {
        			probabilidadeSorteada = rand.nextDouble();
        		} while (probabilidadeSorteada == 0.0d);
        		while (indiceInicio <= indiceFim) {
        			indiceMeio = (indiceInicio + indiceFim) / 2;
        			if (indiceMeio >= 1) {
	        			if (transicoes.get(indiceMeio)._dProb >= probabilidadeSorteada //  + erroAceitavel
	        					&& 
	        					(probabilidadeSorteada > transicoes.get(indiceMeio - 1)._dProb)) {
	        				t = transicoes.get(indiceMeio);
	        				break;
	        			} else if (transicoes.get(indiceMeio)._dProb < probabilidadeSorteada) {
	        				indiceInicio = indiceMeio + 1;
	        			} else {
	        				indiceFim = indiceMeio - 1;
	        			}
        			} else {
        				t = transicoes.get(indiceMeio);
        				break;
        			}
        		}
        	}
            
            if (t != null) {
            	e = t.nextRepresentant;
            }
        }

        double valorBloco = getValorBloco (e);
        e = mdp.setRepresentant(valorBloco, e);
        
        return e;
    }
	
	public double getValorBloco (ArrayList <Boolean> assign) {
		if (assign != null) {
			assign.remove(0);
			double valorBloco = _context.evaluate(stochasticBisimulation, assign);
			assign.add(0, null);
			return valorBloco;
		} else {
			return -1;
		}
	}
	
	
	private int NegativeAdd(int id) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
    	if(Fr == null) {
    		ADDNode nodeKey=_context.getNode(id);
    		if (nodeKey != null) {
	    		if(nodeKey instanceof ADDINode) {
		    		Integer Fh=NegativeAdd(((ADDINode)nodeKey)._nHigh);
		    		Integer Fl=NegativeAdd(((ADDINode)nodeKey)._nLow);
		    		Integer Fvar= ((ADDINode)nodeKey)._nTestVarID;
		    		Fr=_context.getINode(Fvar,Fl,Fh, true);
		    		reduceRemapLeavesCache.put(id, Fr);
		    	} else {
	    			ADDDNode nod = (ADDDNode) nodeKey;
	    			return _context.getConstantNode(nod._dUpper > 0 ? 0d : 1d);
	    		}
    		} else {
    			System.out.println("nodeKey nulo => ID = " + id);
    			// _context.getGraph(id).launchViewer();
    		}
    	}
    	return Fr;
	}
	
	private int computeSuccesors(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
		Integer multCPTs = _context.getConstantNode(1d);
		Integer xiprime;
		
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();

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

		return multCPTs;
	}
	
	private int computeSuccesorsDD(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
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
	

	
	public ArrayList<Boolean> chooseStateOpenQueue() {
		int ADD = _sOpen.poll();
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		int num = _context._alOrder.size();
		int vars = num/2;
		for (int i = 0; i <= num; i++)
			assign.add(i < vars  ? true : null);
		// _context.getGraph(ADD).launchViewer();
		assign = ChooseStateAdd(_context.getNode(ADD), assign, 1d);
		ADD = DDUtils.UpdateValue(_context, ADD, assign, 0d);
		_nOpenAdd = DDUtils.UpdateValue(_context, _nOpenAdd, assign, 0d);
		if (ADD != _context.getConstantNode(0d))
			_sOpen.offer(ADD);
		return assign;
	}
	
	
	/**
	 * Find All Reachable States - Extends checkSolved (Mijail)
	 * @param cur_state
	 * @param epsilon
	 * @return
	 * @throws TimeOutException
	 * 
	 */
	private int findAllReachableStates (ArrayList <Boolean> cur_state, int horizon) {
		System.out.println("Looking for all reachable states considering the initial state: " + cur_state);
		System.out.println("Finite Horizon (h = " + horizon + ")");
		boolean debug = false;
		
		_sOpen = new LinkedList<Integer>();
		_nClosedAdd = _context.getConstantNode(0);
		LinkedList <ArrayList<Boolean>> closed = new LinkedList <ArrayList<Boolean>>();
		_nClosed = 0;
		_nOpenAdd = _context.getConstantNode(0);		
		HashSet <ArrayList <Boolean>> reachableStates = new HashSet <ArrayList <Boolean>>();
		HashMap <ArrayList <Boolean>, Integer> stateToHorizon = new HashMap <ArrayList <Boolean>, Integer> ();
		HashMap <Integer, HashSet<ArrayList<Boolean>>> horizonToState = new HashMap <Integer, HashSet<ArrayList<Boolean>>>(); 
		
		if (!closed.contains(cur_state)) {
			stateToHorizon.put(cur_state, 0);
			HashSet <ArrayList <Boolean>> statesInHorizon = new HashSet <ArrayList <Boolean>> ();
			statesInHorizon.add(cur_state);
			horizonToState.put(0, statesInHorizon);
			_nOpenAdd = DDUtils.UpdateValue(_context, _nOpenAdd, cur_state, 1);
			_sOpen.offer(_nOpenAdd);
		}
		
		int currentHorizon;
		while (!_sOpen.isEmpty()) {
			cur_state = chooseStateOpenQueue();
			currentHorizon = stateToHorizon.get(cur_state);
			if (currentHorizon == horizon) {
				_nClosedAdd = DDUtils.UpdateValue(_context, _nClosedAdd, cur_state, 1);
				closed.offer(cur_state);
				// System.out.println(">>> state " + cur_state + " closed. h = " + currentHorizon);
				_nClosed++;
				if (_nClosed % 1000 == 0) {
					System.out.println("Closed States: " + _nClosed);
				}
				continue;
			}
			
			_nClosedAdd = DDUtils.UpdateValue(_context, _nClosedAdd, cur_state, 1);
			closed.offer(cur_state);
			_nClosed++;
			if (_nClosed % 1000 == 0) {
				System.out.println("Closed States: " + _nClosed);
			}
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			
			for (Action a : _hmActionName2Action.values()) {
				int sucessors = computeSuccesorsDD(cur_state, a._hmVarID2CPT);
				// _context.getGraph(sucessors).launchViewer();
				currentHorizon = stateToHorizon.get(cur_state);
				HashMap<ArrayList<Boolean>, Double> allPaths = getAllPaths(sucessors, false);
				for (ArrayList <Boolean> assignment : allPaths.keySet()) {
					Double value = allPaths.get(assignment);
					if (value > 0.0d) {
						assignment.remove(0);
						int originalSize = assignment.size();
						for (int i = 0; i <= originalSize; i++) {
							assignment.add(null);
						}
							
						ArrayList <ArrayList<Boolean>> statesInAssignment = new ArrayList <ArrayList<Boolean>>();
						ArrayList <ArrayList<Boolean>> completeStates = new ArrayList <ArrayList <Boolean>> ();
						statesInAssignment.add(assignment);
						while (!statesInAssignment.isEmpty()) {
							boolean complete = true;
							assignment = statesInAssignment.remove(0);
							for (int i = 0; i < originalSize; i++) {
								if (assignment.get(i) == null) {
									complete = false;
									ArrayList <Boolean> assignmentTrue = (ArrayList<Boolean>) assignment.clone();
									ArrayList <Boolean> assignmentFalse = (ArrayList<Boolean>) assignment.clone();
									assignmentTrue.set(i, true);
									assignmentFalse.set(i, false);
									statesInAssignment.add(assignmentTrue);
									statesInAssignment.add(assignmentFalse);
									break;
								}
							}
							
							if (complete) {
								completeStates.add(assignment);
							}
						}
							
						for (ArrayList <Boolean> completeState : completeStates) {
							if (!stateToHorizon.containsKey(completeState)) {
									stateToHorizon.put(completeState, currentHorizon + 1);
							}
							
							if (debug) {
								if (horizonToState.get(currentHorizon + 1) != null) {
									HashSet <ArrayList <Boolean>> statesInHorizon = horizonToState.get(currentHorizon + 1);
									statesInHorizon.add(completeState);
									horizonToState.put(currentHorizon + 1, statesInHorizon);
								} else {
									HashSet <ArrayList <Boolean>> statesInHorizon = new HashSet <ArrayList <Boolean>>();
									statesInHorizon.add(completeState);
									horizonToState.put(currentHorizon + 1, statesInHorizon);
								}
							}
						}
					}
				}
				
				
				reduceRemapLeavesCache = new Hashtable();
				// System.out.println("MemDisplay: " + MemDisplay());
				int AB = _context.applyInt(sucessors, NegativeAdd(_nOpenAdd), DD.ARITH_PROD);
				reduceRemapLeavesCache = new Hashtable();
				AB = _context.applyInt(AB, NegativeAdd(_nClosedAdd), DD.ARITH_PROD);
				_nOpenAdd = _context.applyInt(_context.applyInt(_nOpenAdd, AB, DD.ARITH_SUM), _context.applyInt(_nOpenAdd, AB, DD.ARITH_PROD), DD.ARITH_MINUS);
				
				if (AB != _context.getConstantNode(0d)) {
				 	_sOpen.offer(AB);
				}
			}
		}
		reachableStates.addAll(closed);
		showReachableStates (reachableStates);
		reachableStatesSize = reachableStates.size();
		if (debug) {
			printNumberOfReachableStatesPerHorizon (horizonToState);
		}
		return _nClosedAdd;
	}
	
	public void printNumberOfReachableStatesPerHorizon (HashMap <Integer, HashSet<ArrayList<Boolean>>> horizonToStates) {
		for (int i = 0; i < 40; i++) {
			System.out.println(i + "\t" + ((horizonToStates.get(i) != null) ? horizonToStates.get(i).size() : " NULL "));
		}
	}
	
		
	public void showReachableStates (HashSet <ArrayList <Boolean>> reachableStates) {
		System.out.println("All reachable states - Size: " + reachableStates.size());
		if (reachableStates.size() <= 32) { 
			for (ArrayList <Boolean> state : reachableStates) {
				System.out.println(state);
			}
		}
		// _context.getGraph(_nClosedAdd).launchViewer();
	}

	double maxResidual;
	private String SEPARATOR;
	private String OS;
	/**
	 * Mï¿½todo verifica se o estado atual jï¿½ convergiu. Para isso, olha os
	 * estados seguinte e verifica se todos jï¿½ convergiram. Utilizado na
	 * implementaï¿½ï¿½o do (LRTDP). Obs: Jï¿½ foi adaptado para funcionar com R(s,a).
	 * 
	 * @param mdp
	 * @param estado
	 * @param bellmanError
	 * @param pi
	 * @return
	 */
	
	
	public boolean checkSolved(MDP mdp, ArrayList <Boolean> estado, double bellmanError) {

		boolean rv = true;

		Stack<ArrayList <Boolean>> open = new Stack<ArrayList <Boolean>>();
		Stack<ArrayList <Boolean>> closed = new Stack<ArrayList <Boolean>>();
		
		if (!solved.get(estado)) {
			open.push(estado);
		}

		while (!open.isEmpty()) {
			estado = open.pop();

			closed.push(estado);

			ActionTransition at = getGreedyAction(estado);
			double residual = Math.abs(valueFunction.get(estado) - at.getQValue());
			if (residual > bellmanError) {
				rv = false;
				continue;
			}
			
			// estado = updateState(estado);
			
			ArrayList<ProbState> transicoes = at.getTransitions();
			ArrayList<ArrayList <Boolean>> uniao = new ArrayList<ArrayList <Boolean>>();
			uniao.addAll(closed);
			uniao.addAll(open);
			for (int j = 0; j < transicoes.size(); j++) {
				ProbState t = transicoes.get(j);
				double probabilidade = t._dProb;
				if (j >= 1) {
					ProbState tAnterior = transicoes.get(j - 1);
					probabilidade -= tAnterior._dProb;
				}
				
				if (probabilidade > 0) {
					@SuppressWarnings("unchecked")
					ArrayList <Boolean> alStateClone = (ArrayList<Boolean>) t.nextRepresentant.clone();
					
					if (!solved.get(alStateClone) && !uniao.contains(alStateClone)) {
						open.push(alStateClone);
						uniao.add(alStateClone);
					}
				}
			}
		}

		if (rv == true) {
			for (ArrayList <Boolean> estadoResolvido : closed) {
				solved.put(estadoResolvido, true);
			}
		} else {
			while (!closed.isEmpty()) {
				estado = closed.pop();
				estado = updateState(estado);
				if (estado.equals(initialState)) {
					double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
					try {
						// writeToLog("LRTDPCheckSolved for Trial: " + trials);
						writeToLog(instant + "	" + valueFunction.get(estado));
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		}

		// System.out.println ("Fim CheckSolved");

		return rv;
	}
	
	private double getMinRecompensa(
			HashSet<ArrayList<Boolean>> validAssignments, Action action) {

		double minRecompensa = Double.MAX_VALUE;

		for (ArrayList<Boolean> assignment : validAssignments) {
			double recompensaAtual = (double) _context.evaluate(action._reward,
					assignment);
			if (recompensaAtual < minRecompensa) {
				minRecompensa = recompensaAtual;
			}
		}
		return minRecompensa;
	}

	private double getMaxRecompensa(
			HashSet<ArrayList<Boolean>> validAssignments, Action action) {

		double maxRecompensa = -Double.MAX_VALUE;
		for (ArrayList<Boolean> assignment : validAssignments) {
			double recompensaAtual = (double) _context.evaluate(action._reward,
					assignment);
			if (recompensaAtual > maxRecompensa) {
				maxRecompensa = recompensaAtual;
			}
		}
		return maxRecompensa;
	}


	/**
	 * Receives a homogeneous partition and returns a flat MDP induced by the
	 * partition.
	 * 
	 * @param finalPartition
	 * @return
	 * 
	 *         public MDP loadFlatMDP (ArrayList <Integer> finalPartition) {
	 *         bmdp = new BMDP(); bmdp.setFatorDeDesconto ((double) _dDiscount);
	 *         bmdp.setErroMaximoPermitido(0.00001f);
	 * 
	 *         String statePrefix = "s"; for (int i = 0; i <
	 *         finalPartition.size(); i++) { EstadoBMDP s = new
	 *         EstadoBMDP(statePrefix + i);
	 * 
	 *         // _context.getGraph(finalPartition.get(i)).launchViewer();
	 *         HashMap <ArrayList <Boolean>, Double> truthAssignments =
	 *         getTruthAssignments(finalPartition.get(i)); for (ArrayList
	 *         <Boolean> assignment : truthAssignments.keySet()) { //
	 *         System.out.println("Assignment: " + assignment);
	 *         s.adicionaAtribuicao(assignment); } bmdp.adicioneEstado (s); }
	 * 
	 *         for (int i = 0; i < finalPartition.size(); i++) { //
	 *         System.out.println(statePrefix + i); EstadoBMDP s =
	 *         bmdp.getEstado(statePrefix + i);
	 * 
	 *         for (CString a : _hmActionName2Action.keySet()) { Action action =
	 *         _hmActionName2Action.get(a); String actionName = a._string; //
	 *         System.out.println(actionName); ArrayList <Boolean> assignment =
	 *         s.getAtribuicao(); // System.out.println("Assignment = " +
	 *         assignment); ArrayList <Boolean> atribb = new ArrayList
	 *         <Boolean>(assignment.subList(1, assignment.size()));
	 * 
	 *         int atribbSize = atribb.size(); for (int j = 0; j < atribbSize;
	 *         j++) { atribb.add(null); }
	 * 
	 *         double recompensa = (double) _context.evaluate(action._reward,
	 *         atribb); Acao acao = new Acao (actionName, recompensa);
	 * 
	 *         ArrayList <Transicao> transicoes = computeSuccesorsProbEnum(s,
	 *         atribb, action._hmVarID2CPT, action._csActionName, true);
	 *         acao.setTransicoes (transicoes); s.adicionaAcao(acao); }
	 *         mdp.adicioneEstado(s); } return mdp; }
	 */

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
			this.OS = "Win";
		}
		
		if (OS.indexOf("nix") >= 0 || OS.indexOf("nux") >= 0 || OS.indexOf("aix") >= 0) {
			System.out.println("OS = Unix");
			SEPARATOR = new String("/");
			this.OS = "Unix";
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
					// 		_context.getMaxValue(a._reward));
					// maxReward = Math.max (maxReward, _context.getMaxValue(a._reward));
					// minReward = Math.min (minReward, _context.getMinValue(a._reward));
				}
				double value_range = _dRewardRange;

				value_range = (_dDiscount < 1d) ? value_range / (1d - _dDiscount) // being lazy: assume infinite
											// horizon
				: _nHorizon * value_range; // assume max reward over horizon*/

				heuristicaAdmissivel = value_range;

				System.out.println("Heuristica admissï¿½vel: "
						+ heuristicaAdmissivel);
				// System.exit(0);
			} catch (Exception e) {
				System.err.println("Exception at " + _nIter + " iterations.");
				e.printStackTrace(System.err);
				System.exit(1);
			} catch (Throwable t) {
				System.out.println("Throwable lanï¿½ado. Subclasse de java.lang.Error: " + t.getMessage());
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
						pi = new HashMap <ArrayList <Boolean>, ActionTransition>();
					}
					System.out.println(">>> MDP in" +
							"stantiated.");
				}
			}
		}
	}
	

	
	public void setInstanceName (String instanceName) {
		this.instanceName = instanceName;
	}
	
	public void timeInfo (Cronometro reachabilityTime, Cronometro bisimulationTime, Cronometro lrtdpTime, double reward) {
		StringBuffer timeInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (timeInfoContent);
		timeInfoContent.append("INSTANCE=" + _sInstanceName + "\n");
		if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
			timeInfoContent.append("REACHABILITY_TIME=" + ((double) reachabilityTime.getTotalMilisegundos() / 1000.0d) + "\n");
		}
		
		if (GET_NUMBER_OF_REACHABLE_STATES) {
			timeInfoContent.append("REACHABLE_STATES=" + reachableStatesSize + "\n");
		}
		
		timeInfoContent.append("HOMOGENEOUS_PARTITION_SIZE=" + partitionSize + "\n");
		
		if (ONLY_BISIMULATION) {
			timeInfoContent.append("BISIMULATION_TIME=" + ((double) bisimulationTime.getTotalMilisegundos() / 1000.0d) + "\n");
			if (MODEL_MINIMIZATION) {
				geradorDeArquivo.geraArquivo("ReachMMFS_OnlyBisimulation" + SEPARATOR + _sInstanceName + "_Time.txt");
			} else {
				if (ONLY_USEFUL_PARTITIONS) {
					geradorDeArquivo.geraArquivo("ReachMRFS_OnlyBisimulation" + SEPARATOR + _sInstanceName + "_Time.txt");
				} else {
					geradorDeArquivo.geraArquivo("ReachMRFSRepeatPartitions_OnlyBisimulation" + SEPARATOR + _sInstanceName + "_Time.txt");
				}
			}
		} else {
			timeInfoContent.append("BISIMULATION_TIME=" + ((double) bisimulationTime.getTotalMilisegundos() / 1000.0d) + "\n");
			timeInfoContent.append("PLANNER_TIME=" + ((double) lrtdpTime.getTotalMilisegundos() / 1000.0d) + "\n");
			timeInfoContent.append("REWARD=" + reward + "\n");
			timeInfoContent.append("V*(s0)=" + valueFunctionS0 + "\n");
			if (ONLY_USEFUL_PARTITIONS) {
				if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
					if (ONLY_BISIMULATION) {
						geradorDeArquivo.geraArquivo("ReachabilityBisimulationImpl2Time" + SEPARATOR + _sInstanceName + "_Time.txt");
					} else if (!ONLY_BISIMULATION && MODEL_MINIMIZATION){
						geradorDeArquivo.geraArquivo("ReachabilityMMPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
					} else if (!ONLY_BISIMULATION && !MODEL_MINIMIZATION){
						geradorDeArquivo.geraArquivo("ReachabilityMMPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
					}
				} else {
					if (ONLY_BISIMULATION) {
						geradorDeArquivo.geraArquivo("BisimulationTime" + SEPARATOR + _sInstanceName + "_Time.txt");
					} else {
						geradorDeArquivo.geraArquivo("BisimulationPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
					}
				}
			} else {
				geradorDeArquivo.geraArquivo("OriginalBisimulationTime" + SEPARATOR + _sInstanceName + "_Time.txt");
			}	
		}
	}
	
	public void bisimulationInfo(Integer stochasticBisimulation, Cronometro c) {
		StringBuffer bisimulationInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (bisimulationInfoContent);
		
		
		bisimulationInfoContent.append("===============================================================\n");
		bisimulationInfoContent.append("===================== Bisimulation Report =====================\n");
		bisimulationInfoContent.append("===============================================================\n");
		bisimulationInfoContent.append("Instance: " + _sInstanceName + "\n");
		bisimulationInfoContent.append("Number of state variables: " + problemDescription.getNumVars() + "\n");
		bisimulationInfoContent.append("Number of states: " + problemDescription.getNumStates() + "\n");
		bisimulationInfoContent.append("Number of actions: " + problemDescription.getNumActions() + "\n");
		bisimulationInfoContent.append("Epsilon for aggregation: " + EPSILON_APROXIMATION + "\n");
		bisimulationInfoContent.append("Ignore noop \'action\': " + IGNORE_NOOP + "\n");
		bisimulationInfoContent.append("Reward Partition' Size: " + rewardPartitionSize + "\n");
		if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
			bisimulationInfoContent.append("Number of Reachable States: " + reachableStatesSize + "\n");
		}
		bisimulationInfoContent.append("Stochastic Bisimulation Partition' size: " + partitionSize + "\n");
		BigDecimal partitionSizeBD = new BigDecimal(((double) partitionSize));
		bisimulationInfoContent.append("Ratio of the reduced model w.r.t. the original: " + partitionSizeBD.divide (problemDescription.getNumStates()) + "\n");
		HashSet varsMentionedInBisimulation = (HashSet) _context.getGIDs(stochasticBisimulation);
		bisimulationInfoContent.append("Number of vars in the stochastic bisimulation partitionn: " + varsMentionedInBisimulation.size() + "\n");
		int stochasticBisimulationADDHeight = ADDHeight(_context.getNode(stochasticBisimulation));
		bisimulationInfoContent.append("Stochastic Bisimulation's ADD Height: " + stochasticBisimulationADDHeight + "\n");
		bisimulationInfoContent.append("Leaves of all transition function: " + getLeavesOfTransitionFunction() + "\n");
		bisimulationInfoContent.append("Leaves equal to zero in all transition functions: " + getLeavesEqualToZero() + "\n");
		bisimulationInfoContent.append("Proportion of zero in the transition DD's: " + (double) getLeavesEqualToZero() / (double) getLeavesOfTransitionFunction() + "\n");
		bisimulationInfoContent.append("All MDP Partitions: " + _allMDPADDs.size() + "\n");
		if (ONLY_USEFUL_PARTITIONS) {
			bisimulationInfoContent.append("Useful Partitions for bisimulation: " + usefulPartitionsOriginalSize + "\n");
		}
		
		bisimulationInfoContent.append("Time to compute bisimulation (s): " + ((double) c.getTotalMilisegundos() / 1000.0d) + "\n");
		// bisimulationInfoContent.append(partitionsInfo());
		bisimulationInfoContent.append("===============================================================\n");
		bisimulationInfoContent.append("===============================================================\n\n");
		if (ONLY_USEFUL_PARTITIONS) {
			if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
				geradorDeArquivo.geraArquivo("bisimulationWithReachabilityInfoLogs" + SEPARATOR + _sInstanceName + "_bisimulationInfo.txt");
			} else {
				geradorDeArquivo.geraArquivo("bisimulationWoRedundancyInfoLogs" + SEPARATOR + _sInstanceName + "_bisimulationInfo.txt");
			}
		} else {
			geradorDeArquivo.geraArquivo("bisimulationInfoLogs" + SEPARATOR + _sInstanceName + "_bisimulationInfo.txt");
		}
	}

	/**
	 * Devolve a altura de um ADD baseado no conceito de altura para ï¿½rvores binï¿½rias.
	 * @param node
	 * @return
	 */
	public int ADDHeight (ADDNode node) {
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				ADDNode highSon = _context.getNode(internalNode._nHigh);
				ADDNode lowSon = _context.getNode(internalNode._nLow);
				int highSonHeight = ADDHeight (highSon);
				int lowSonHeight = ADDHeight (lowSon);
				if (highSonHeight < lowSonHeight) {
					return lowSonHeight + 1;
				} else {
					return highSonHeight + 1;
				}
			} else {
				return 0;
			}
		} else {
			return -1;
		}
	}
	

	/**
	 * Performs an inorder search in the given ADD and return the mapping
	 * (assignment -> value) for all possible assignments.
	 * 
	 * @param node
	 * @param assign
	 * @param estadoRecompensa
	 */
	public void inOrderSearch(ADDNode node, ArrayList<Boolean> assign,
			HashMap<ArrayList<Boolean>, Double> estadoRecompensa) {
		if (node != null) {
			if (node instanceof ADDINode) {
				ADDINode internalNode = (ADDINode) node;
				int level = ((Integer) _context._hmGVarToLevel.get(new Integer(
						((ADDINode) internalNode)._nTestVarID))).intValue();
				Integer var_id = (Integer) _context._alOrder.get(level);
				// String var = (String) _context._hmID2VarName.get(var_id);
				// System.out.println ("var_id: " + var_id + " - var: " + var);

				ADDNode lowNode = _context.getNode(internalNode._nLow);
				ADDNode highNode = _context.getNode(internalNode._nHigh);

				// Expande a subarvore low (false)
				ArrayList<Boolean> assign1 = (ArrayList<Boolean>) assign
						.clone();
				ArrayList<Boolean> assign2 = (ArrayList<Boolean>) assign
						.clone();

				assign1.set(var_id, new Boolean(false));
				inOrderSearch(lowNode, assign1, estadoRecompensa);

				// Expande a subarvore high (true)
				assign2.set(var_id, new Boolean(true));
				inOrderSearch(highNode, assign2, estadoRecompensa);

			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				if (Math.abs(leaf._dLower - leaf._dUpper) < 0.0000000001d) {
					// System.out.println("_dLower e _dUpper sï¿½o praticamente iguais.");
					// System.out.println("Assign: " + assign);
					// System.out.println("_dLower = _dUpper = " +
					// leaf._dLower)
					if (leaf._dLower != 0.0d) {
						Double recompensa = leaf._dLower;
						estadoRecompensa.put((ArrayList<Boolean>) assign.clone(),
							recompensa);
					}
				} else {
					// Calcula a mï¿½dia.
					// System.out.println("_dLower = " + leaf._dLower +
					// " _dUpper = " + leaf._dUpper);
					Double recompensa = (leaf._dLower + leaf._dUpper) / 2;
					estadoRecompensa.put((ArrayList<Boolean>) assign.clone(),
							recompensa);
				}
			} else if (node instanceof ADDBNode) {
				ADDBNode leaf = (ADDBNode) node;
				if (leaf._bVal == true) {
					Double recompensa = 1.0d;
					estadoRecompensa.put((ArrayList<Boolean>) assign.clone(),
							recompensa);
				}
			}
		}
	}

	public HashMap<ArrayList<Boolean>, Double> getTruthAssignments(
			int decisionDiagramID) {
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		double tolerance = 0.0000000001;
		HashMap<ArrayList<Boolean>, Double> atribuicoes = new HashMap<ArrayList<Boolean>, Double>();
		HashMap<ArrayList<Boolean>, Double> atribuicoesDoBloco = new HashMap<ArrayList<Boolean>, Double>();
		for (int i = 0; i <= _translation._alStateVars.size(); i++) {
			assign.add(null);
		}

		// Realizes a search using the inorder traversal (left-center-right).
		// Used to extract the reward from the ADD.
		inOrderSearch(_context.getNode(decisionDiagramID), assign, atribuicoes);

		for (ArrayList<Boolean> assignInstance : atribuicoes.keySet()) {
			if (Math.abs(1.0d - atribuicoes.get(assignInstance)) <= tolerance) {
				atribuicoesDoBloco.put(assignInstance,
						Math.abs(atribuicoes.get(assignInstance)));
			}
		}

		return atribuicoesDoBloco;

	}

	/**
	 * Given a master state and a partition, return the relevant vars' indexes
	 * to the block.
	 * 
	 * @param masterState
	 * @param partition
	 * @return
	 */
	public HashSet<Integer> geIndexesOfStateVarsFromBlock(
			ArrayList<Boolean> masterState,
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition) {
		HashSet<Integer> indexesOfStateVarsFromBlock = new HashSet<Integer>();
		HashSet<ArrayList<Boolean>> statesFromBlock = getStatesFromBlock(
				masterState, partition);
		for (ArrayList<Boolean> state : statesFromBlock) {
			for (int i = 1; i < state.size(); i++) {
				if (state.get(i) != null) {
					indexesOfStateVarsFromBlock.add(new Integer(i));
				}
			}
		}
		return indexesOfStateVarsFromBlock;
	}

	/**
	 * Given a partition and a master states, returns all state in the block
	 * represented by the master state (including the master state).
	 * 
	 * @param masterState
	 * @param partition
	 * @return statesFromBlock
	 */
	public HashSet<ArrayList<Boolean>> getStatesFromBlock(
			ArrayList<Boolean> masterState,
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition) {
		HashSet<ArrayList<Boolean>> statesFromBlock = new HashSet<ArrayList<Boolean>>();
		for (ArrayList<Boolean> currentState : partition.keySet()) {
			if (partition.get(currentState).equals(masterState)) {
				statesFromBlock.add(currentState);
			}
		}
		return statesFromBlock;
	}

	/**
	 * Given a partition represented as a forest, return the master states
	 * (states that represents each block in the partition).
	 * 
	 * @param partition
	 * @return
	 */
	public HashSet<ArrayList<Boolean>> getMasterStates(
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition) {
		HashSet<ArrayList<Boolean>> masterStates = new HashSet<ArrayList<Boolean>>();
		for (ArrayList<Boolean> state : partition.keySet()) {
			if (state.equals(partition.get(state))) {
				// this state is a master state
				masterStates.add(state);
			}
		}
		return masterStates;
	}

	/**
	 * Extract all assignments of a decision diagram and the paths that carry to
	 * the different values (except those in which the leaves are equal to zero). 
	 * 
	 * @param decisionDiagramID
	 * @return
	 */
	public HashMap<ArrayList<Boolean>, Double> getAllPaths(int decisionDiagramID, boolean reachableStates) {
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		HashMap<ArrayList<Boolean>, Double> atribuicoes = new HashMap<ArrayList<Boolean>, Double>();
		
		if (!reachableStates) {
			for (int i = 0; i <= (2 * _translation._alStateVars.size() + 1); i++) {
				assign.add(null);
			}
		} else {
			for (int i = 0; i <= _translation._alStateVars.size(); i++) {
				assign.add(null);
			}
		}

		// _context.getGraph(decisionDiagramID).launchViewer();

		// Realizes a search using the inorder traversal (left-center-right).
		// Used to extract the reward from the ADD.
		inOrderSearch(_context.getNode(decisionDiagramID), assign, atribuicoes);
		
		return atribuicoes;
	}

	public LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> getRewardPartitionFromAssignments(
			HashMap<ArrayList<Boolean>, Double> atribuicoes) {
		double erroPermitido = 0.0000000001;

		LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition = new LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>>();

		int assignmentWithoutBlock = 0;
		assignmentWithoutBlock = atribuicoes.size();
		
		for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
			partition.put(currentAssign, null);
			// assignmentWithoutBlock++;
		}

		int i = 0;
		while (assignmentWithoutBlock > 0) {
			// System.out.println("\tgetRewardPartition - Iteration " + i++);
			if (EPSILON_APROXIMATION < erroPermitido || (EPSILON_APROXIMATION > erroPermitido && !APROXIMATION_IN_REWARD)) {
				for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
					if (partition.get(currentAssign) == null) {
						boolean existsABlock = false;
						for (ArrayList <Boolean> masterInPartition : partition.values()) {
							if (partition.get(masterInPartition) != null) {
								if (Math.abs (atribuicoes.get(currentAssign) - atribuicoes.get(masterInPartition)) <= erroPermitido) {
									partition.put(currentAssign, partition.get(masterInPartition));
									existsABlock = true;
									break;
								}
							}
						}
						
						if (!existsABlock) {
							partition.put(currentAssign, currentAssign);
						}
						
						assignmentWithoutBlock--;
					}
				}
			} else {
				// Funciona, mas nï¿½o com |X| >= 16
				for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
					if (partition.get(currentAssign) == null) {
						partition.put(currentAssign, currentAssign);
						assignmentWithoutBlock--;
						// System.out.println("AssignmentsWithoutBlock: " + assignmentWithoutBlock);
						double currentAssignValue = atribuicoes.get(currentAssign);
						for (ArrayList<Boolean> anotherAssign : atribuicoes.keySet()) {
							if (!currentAssign.equals(anotherAssign) && (partition.get(anotherAssign) == null)) {
								double anotherAssignValue = atribuicoes.get(anotherAssign);
								if (Math.abs(currentAssignValue - anotherAssignValue) <= EPSILON_APROXIMATION + erroPermitido) {
									partition.put(anotherAssign, currentAssign);
									assignmentWithoutBlock--;
								}
							}
						}
					} else {
						ArrayList<Boolean> masterInPartition = partition.get(currentAssign);
						for (ArrayList<Boolean> anotherAssign : atribuicoes.keySet()) {
							if (partition.get(anotherAssign) != null) {
								if (!anotherAssign.equals(masterInPartition) && (partition.get(anotherAssign).equals(masterInPartition))) {
									double currentAssignValue = atribuicoes.get(currentAssign);
									double anotherAssignValue = atribuicoes.get(anotherAssign); 
									if (Math.abs(currentAssignValue - anotherAssignValue) > EPSILON_APROXIMATION + erroPermitido) {
										partition.put(anotherAssign, null);
										assignmentWithoutBlock++;
									} else {
										continue;
									}
								}
							}
						}
					}
				} 
				
				/* Forma maais eficiente: mas incorreta
				for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
					if (partition.get(currentAssign) == null) {
						boolean existsABlock = false;
						for (ArrayList <Boolean> masterInPartition : partition.values()) {
							if (partition.get(masterInPartition) != null) {
								if (Math.abs (atribuicoes.get(currentAssign) - atribuicoes.get(masterInPartition)) <= EPSILON_APROXIMATION + erroPermitido) {
									partition.put(currentAssign, partition.get(masterInPartition));
									existsABlock = true;
									break;
								}
							}
						}
						
						if (!existsABlock) {
							partition.put(currentAssign, currentAssign);
						}
						
						assignmentWithoutBlock--;
					} else {
						ArrayList <Boolean> masterOfCurrentAssign = partition.get(currentAssign);
						for (ArrayList <Boolean> anotherAssign : atribuicoes.keySet()) {
							if (!anotherAssign.equals(masterOfCurrentAssign)) {
								if (partition.get(anotherAssign) != null && partition.get(anotherAssign).equals(masterOfCurrentAssign)) {
									double currentAssignValue = atribuicoes.get(currentAssign);
									double anotherAssignValue = atribuicoes.get(anotherAssign); 
									if (Math.abs(currentAssignValue - anotherAssignValue) > EPSILON_APROXIMATION + erroPermitido) {
										partition.put(anotherAssign, null);
										assignmentWithoutBlock++;
									} else {
										continue;
									}
								}
							}
						}
					}
				}
				*/
			}
		}

		return partition;
	}

	/**
	 * Get a map of assignments to values and creates a partition in which each
	 * block has assignments with (or aproximately) the same value.
	 * 
	 * @param atribuicoes
	 * @param epsilonAproximation
	 * @return
	 */
	public LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> getPartitionFromAssignments(
			HashMap<ArrayList<Boolean>, Double> atribuicoes) {
		double erroPermitido = 0.0000000001;

		LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition = new LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>>();
		for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
			partition.put(currentAssign, null);
		}

		// Create a partition represented as a forest with the array obtained
		// early.
		HashSet<ArrayList<Boolean>> mastersInPartition = new HashSet<ArrayList<Boolean>>();
		for (ArrayList<Boolean> currentAssign : atribuicoes.keySet()) {
			if (partition.get(currentAssign) == null) {
				for (ArrayList<Boolean> anotherAssign : atribuicoes.keySet()) {
					if (!(currentAssign.equals(anotherAssign))) {
						if (partition.get(anotherAssign) != null) {
							if (Math.abs(atribuicoes.get(currentAssign)
									- atribuicoes.get(anotherAssign)) <= erroPermitido) {
								partition.put(currentAssign,
										partition.get(anotherAssign));
							}
						}
					} else {
						continue;
					}
				}

				if (partition.get(currentAssign) == null) {
					partition.put(currentAssign, currentAssign);
					mastersInPartition.add(currentAssign);
				}
			}
		}

		return partition;
	}


	
	private void freeAllPrimes (LinkedHashMap <Integer, Boolean> primeUsed) {
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				primeUsed.put(prime, false);
			} else {
				break;
			}
		}
	}
	
	private int countPrimesUsed (LinkedHashMap <Integer, Boolean> primeUsed) {
		int countPrimesUsed = 0;
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				countPrimesUsed++;
			}
		}
		return countPrimesUsed;
	}
	
	private Integer getNextFreePrime (LinkedHashMap <Integer, Boolean> primeUsed) {
		Integer freePrime = null;
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(false)) {
				primeUsed.put(prime, true);
				freePrime = prime;
				break;
			}
		}
		
		if (freePrime == null) {
			missingPrimes++;
			System.out.println("Nï¿½o foi possï¿½vel prosseguir, poucos nï¿½meros primos encontrados.");
			ArrayList <Integer> primeNumbers = soe.getPrimeNumbers(soe.recomputeMappingOfNumbers());
			System.out.println("Mais numeros primos foram encontrados.");
			for (Integer prime : primeNumbers) {
				if (!primeUsed.keySet().contains(prime)) {
					primeUsed.put(prime, false);
				}
			}
			freePrime = getNextFreePrime (primeUsed);
		}
		return freePrime;
	}
	
	private int reduceRemapLeaves(int id) {
		Integer Fr = (Integer)reduceRemapLeavesCache.get(id);
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
	
	private int replaceZerosByBlockIds(int id, HashMap <Double, Integer> oldValueToPrime, boolean remapZeros) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
    	if (Fr == null) {
    		ADDNode nodeKey = _context.getNode(id);
    		if (nodeKey instanceof ADDINode) {
	    		Integer Fh = replaceZerosByBlockIds(((ADDINode)nodeKey)._nHigh, oldValueToPrime, remapZeros);
	    		Integer Fl = replaceZerosByBlockIds(((ADDINode)nodeKey)._nLow, oldValueToPrime, remapZeros);
	    		Integer Fvar = ((ADDINode)nodeKey)._nTestVarID;
	    		Fr  =_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	} else {
    			ADDDNode nod = (ADDDNode)nodeKey;
    			// modificar este trecho para inserir nï¿½mero primo.
    			// necessï¿½rio de um contador global de nï¿½meros primos de forma
    			// que sempre que necessï¿½rio, a contagem seja incrementada e seja
    			// garantido que um nï¿½mero primo diferente serï¿½ obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necessï¿½rio alguma regra para nï¿½o separar blocos...
    			if (oldValueToPrime.get(nod._dUpper) == null) {
    				if (remapZeros) {
    					if (nod._dUpper == 0.0d) {
    						int newValue = getNextFreePrime(primeUsed);
    						oldValueToPrime.put(nod._dUpper, newValue);
    						return _context.getConstantNode(newValue);
    					} else {
    						return _context.getConstantNode(nod._dUpper);
    					}
    				} else {
    					if (nod._dUpper == 0.0d) {
    						int newValue = getNextFreePrime(primeUsed);
        					oldValueToPrime.put(nod._dUpper, newValue);
        					return _context.getConstantNode(newValue);
    					} else {
    						return _context.getConstantNode(nod._dUpper);
    						
    					}
    				}
    			} else {
    				return _context.getConstantNode(oldValueToPrime.get(nod._dUpper));
    			}
    		}
    	}
    	return Fr;
	}
	
	private int reduceRemapLeaves(int id, HashMap <Double, Integer> oldValueToPrime, LinkedHashMap<Integer, Boolean> primeMapping, boolean remapZeros) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
    	if (Fr == null) {
    		ADDNode nodeKey = _context.getNode(id);
    		if (nodeKey instanceof ADDINode) {
	    		Integer Fh = reduceRemapLeaves(((ADDINode)nodeKey)._nHigh, oldValueToPrime, primeMapping, remapZeros);
	    		Integer Fl = reduceRemapLeaves(((ADDINode)nodeKey)._nLow, oldValueToPrime, primeMapping, remapZeros);
	    		Integer Fvar = ((ADDINode)nodeKey)._nTestVarID;
	    		Fr  =_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	} else {
    			ADDDNode nod = (ADDDNode)nodeKey;
    			// modificar este trecho para inserir nï¿½mero primo.
    			// necessï¿½rio de um contador global de nï¿½meros primos de forma
    			// que sempre que necessï¿½rio, a contagem seja incrementada e seja
    			// garantido que um nï¿½mero primo diferente serï¿½ obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necessï¿½rio alguma regra para nï¿½o separar blocos...
    			if (oldValueToPrime.get(nod._dUpper) == null) { // essa folha ainda nï¿½o foi visitada
    				if (remapZeros) {
    					int newValue = getNextFreePrime(primeUsed);
    					oldValueToPrime.put(nod._dUpper, newValue);
    					return _context.getConstantNode(newValue);
    				} else {
    					if (nod._dUpper == 0.0d) {
    						return _context.getConstantNode(0.0d);
    					} else {
    						int newValue = getNextFreePrime(primeUsed);
        					oldValueToPrime.put(nod._dUpper, newValue);
        					return _context.getConstantNode(newValue);
    					}
    				}
    			} else { // folha jï¿½ visitada, utiliza valor existente para nï¿½o separï¿½ quando se considera outros caminhos.
    				return _context.getConstantNode(oldValueToPrime.get(nod._dUpper));
    			}
    		}
    	}
    	return Fr;
	}
	
	private LinkedHashSet<Integer> getEssentialFluents (Integer finalRewardPartition) {
		LinkedHashSet<Integer> essentialFluents = new LinkedHashSet <Integer>();
		LinkedHashSet<Integer> lastIterationEssentialFluents = new LinkedHashSet <Integer>();
		
		ConcurrentLinkedQueue <Integer> essentialFluentsDynamicList = new ConcurrentLinkedQueue <Integer>(); 
		// get the fluents required to represent the reward partition
		essentialFluents.addAll (_context.getGIDs(finalRewardPartition));
		essentialFluentsDynamicList.addAll(essentialFluents);
		
		while (!essentialFluents.equals(lastIterationEssentialFluents)) {
			lastIterationEssentialFluents = new LinkedHashSet (essentialFluents);
			for (CString a : _hmActionName2Action.keySet()) {
				// System.out.println(a);
				Action action = _hmActionName2Action.get(a);
				for (Integer fluent : essentialFluentsDynamicList) {
				// System.out.println("Id = " + fluent + " " + _context._hmID2VarName.get(fluent));
					String varName = (String) _context._hmID2VarName.get(fluent);
					varName = varName + "'";
					Integer nextStateFluent = (Integer) _context._hmVarName2ID
							.get(varName);
					Integer probabilisticTransitionForFluent = action._hmVarID2CPT.get(nextStateFluent);
					Integer probabilitsticTransitionRestricted = _context.restrict(probabilisticTransitionForFluent, nextStateFluent, ADD.RESTRICT_HIGH);
					LinkedHashSet <Integer> tempFluents = new LinkedHashSet <Integer> (_context.getGIDs(probabilitsticTransitionRestricted));
					essentialFluents.addAll(tempFluents);
					for (Integer newFluent : essentialFluents) {
						if (!essentialFluentsDynamicList.contains(newFluent)) {
							essentialFluentsDynamicList.add(newFluent);
						}
					}
							// 	LinkedHashSet <Integer> fluentsFromTransitionProbability = 
				}
			}
		}
		
		if (essentialFluents.size() == _alStateVars.size()) {
			System.out.println("All fluents are essential.");
		}
		
		return essentialFluents;
	}
	
	/**
	 * A generalization of Reasonable Actions used in PROST.
	 * @param a1
	 * @param a2
	 * @return
	 */
	public boolean dominatesOrEquivalent (Action a1, Action a2) {
		boolean a1DominatesA2 = false;
		
		LinkedHashSet <Integer> instanceFluents = new LinkedHashSet <Integer> ();
		for (int i = 1; i <= _context._hmID2VarName.size() / 2; i++) {
			instanceFluents.add(i);
		}
		
		LinkedHashSet <Integer> nextStateFluents = getNextStateFluents(instanceFluents);
		
		if (a1._reward >= a2._reward) {
			boolean transitionRedundant = true;
			for (Integer head_var_gid : nextStateFluents) {
				Integer cptDDForA1 = a1._hmVarID2CPT.get(head_var_gid);
				Integer cptDDForA2 = a2._hmVarID2CPT.get(head_var_gid);
				if (!cptDDForA1.equals(cptDDForA2)) {
					transitionRedundant = false;
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}
	

	/**
	 * This method aggregates the states of a factored (implicit) MDP and
	 * generate an explicit (flat) MDP that has fewer states than the original
	 * MDP.
	 */
	@SuppressWarnings("unchecked")
	public Integer getReducedExplicitMDP(int solverTimeLimit) throws TimeOutException {
		
		System.out.println("MemDisplay at beginning: " + MemDisplay());
		_nTimeLimitSecs = solverTimeLimit;
		_lStartTime = System.currentTimeMillis();
		stochasticBisimulationTime = new Cronometro();
		stochasticBisimulationTime.setStart();
		isADDRedundant = new HashMap <Integer, Boolean>();
		problemDescription = new ProblemDescription (_context, _hmActionName2Action);
		
		System.out.println("Looking for prime numbers... ");
		if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
			soe = new SieveOfEratosthenes((int) (problemDescription.getNumVars() + problemDescription.getNumActions() * problemDescription.getNumVars()) * 100); // valor base vï¿½lido para a maior parte dos problemas abstraï¿½dos.
		} else {
			// soe = new SieveOfEratosthenes((int) (problemDescription.getNumVars() + problemDescription.getNumActions() * problemDescription.getNumVars()) * 500); // valor base vï¿½lido para a maior parte dos problemas abstraï¿½dos.
			soe = new SieveOfEratosthenes(20000000); // testado e funcionando atï¿½ 40.000.000
		}
		
		
		// SieveOfEratosthenes soe = new SieveOfEratosthenes();
		LinkedHashMap <Integer, Boolean> mappingOfNumbers = soe.getMappingOfNumbers();
		primeNumbers = soe.getPrimeNumbers (mappingOfNumbers);
		// soe.printPrimeNumbers(mappingOfNumbers);
		// soe.printPrimeNumbers(mappingOfNumbers);
		System.out.println("Prime numbers found. How many? " + primeNumbers.size());
		// System.out.println("Last prime = " + primeNumbers.get(primeNumbers.size() - 1));
		for (int i = 0; i < primeNumbers.size(); i++) {
			primeUsed.put(primeNumbers.get(i), false);
		}
		
		int maxPrimesUsed = countPrimesUsed (primeUsed);
		System.out.println("|Primes used| = " + maxPrimesUsed);
		
		
		ArrayList<Integer> partitionIntersectionAsBDD = new ArrayList<Integer>();
		
		if (ONLY_USEFUL_PARTITIONS) {
			usefulPartitions = identifyAllRedundantPartitions(_allMDPADDs);
			usefulPartitionsOriginalSize = usefulPartitions.size();
		} else {
			usefulPartitions = (ArrayList<Integer>) _allMDPADDs.clone();
			usefulPartitionsOriginalSize = usefulPartitions.size();
		}
		
		int ddMinReward = -1;
		int ddScale = -1;
		
		if (EPSILON_MODEL_REDUCTION > 0.0d) {
			System.out.println("Approximated stochastic bisimulation...");
			double rewardMin = Double.MAX_VALUE;
			double rewardMax = -Double.MAX_VALUE;

			for (CString a : _hmActionName2Action.keySet()) {
				Action action = _hmActionName2Action.get(a);
				double currentMax = _context.getMax(action._reward);
				double currentMin = _context.getMin(action._reward);
				if (currentMin < rewardMin) {
					rewardMin = currentMin;
				}

				if (currentMax > rewardMax) {
					rewardMax = currentMax;
				}
			}

			ddMinReward = _context.getConstantNode(rewardMin);
			double difference = rewardMax - rewardMin;
			double scale = 1 / difference;
			ddScale = _context.getConstantNode(scale);
		}
		
		HashMap <Action, Integer> newActionRewardMap = new HashMap <Action, Integer>();
		
		for (CString a : _hmActionName2Action.keySet()) {
			System.out.println("- " + a);
			Action action = _hmActionName2Action.get(a);
			Integer newActionReward = null;
			
			if (usefulPartitions.contains(new Integer (action._reward))) {
				if (EPSILON_MODEL_REDUCTION > 0.0d) {
					// _context.getGraph(action._reward).launchViewer();
					newActionReward = _context.applyInt(action._reward,
							ddMinReward, DD.ARITH_MINUS);
					newActionReward = _context.applyInt(newActionReward, ddScale,
							DD.ARITH_PROD);
					// _context.getGraph(newActionReward).launchViewer();
					// other way to reduce the reward partition.
					_context.setPrunePrecision (EPSILON_MODEL_REDUCTION);
					newActionReward = _context.pruneNodes (newActionReward);
					newActionRewardMap.put(action, newActionReward);
					// _context.getGraph(newActionReward).launchViewer();
				}
			}
		}

		// Calculate the intersection among the reward partitions.
		Integer finalRewardPartition = null;
		
		for (CString a : _hmActionName2Action.keySet()) {
			Action action = _hmActionName2Action.get(a);
			// if (action._csActionName._string.equals("noop")) {
			//	_context.getGraph(action._reward).launchViewer();
			// }
			HashMap <Double, Integer> oldValueToPrime = new HashMap <Double, Integer>();
			if (usefulPartitions.contains(action._reward)) {
				if (EPSILON_MODEL_REDUCTION > 0.0d) {
					if (finalRewardPartition == null) {
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = newActionRewardMap.get(action);
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap <Double, Integer>();
						// _context.getGraph(partition).launchViewer();
						Integer newPartition = reduceRemapLeaves (partition, oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = newPartition;
					} else {
						Integer partition = newActionRewardMap.get(action);
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap <Double, Integer>();
						// _context.getGraph(partition).launchViewer();
						Integer newPartition = reduceRemapLeaves (partition, oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context.applyInt(finalRewardPartition, newPartition, ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction (finalRewardPartition, primeUsed, false);
					}
				} else {
					// System.out.println("P^a_R = " + action._csActionName);
					if (finalRewardPartition == null) {
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap <Double, Integer>();
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = reduceRemapLeaves (action._reward, oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = partition;
					} else {
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap <Double, Integer>();
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = reduceRemapLeaves (action._reward, oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context.applyInt(finalRewardPartition, partition, ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction (finalRewardPartition, primeUsed, false);
						
					}
				}
				
				if (ONLY_USEFUL_PARTITIONS) {
					usefulPartitions.remove(new Integer(action._reward));
				}
				
			}
		}
		System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < countPrimesUsed(primeUsed)) {
			maxPrimesUsed = countPrimesUsed(primeUsed);
		}
		
		HashSet leaves = new HashSet();
		// _context.getGraph(finalRewardPartition).launchViewer();
		_context.collectLeaves(finalRewardPartition, leaves);
		rewardPartitionSize = leaves.size();
		System.out.println("Reward Partition computed. Size ? " + rewardPartitionSize);
		
		// System.out.println("Reward Partition ADD's Height = " + ADDHeight(_context.getNode(finalRewardPartition)));
		// System.out.println("Number of Reward Partition GIDs = " + _context.getGIDs(finalRewardPartition).size());
		freeAllPrimes(primeUsed);
		finalRewardPartition = getPartitionFromFunction (finalRewardPartition, primeUsed, false);
		System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < countPrimesUsed(primeUsed)) {
			maxPrimesUsed = countPrimesUsed(primeUsed);
		}
		// _context.getGraph(finalRewardPartition).launchViewer();

		// Refine the partition based on the probability of transitions for
		// each action.
		Integer newPartition = finalRewardPartition;
		Integer oldPartition;
		
		LinkedHashSet <Integer> instanceFluents = new LinkedHashSet <Integer> ();
		if (ONLY_ESSENTIAL_VARS ) {
			instanceFluents.addAll(getEssentialFluents(finalRewardPartition));
		} else { // ALL VARS
			for (int i = 1; i <= _context._hmID2VarName.size() / 2; i++) {
			 	instanceFluents.add(i);
			}
		}
		
		HashMap <Action, Integer> partitionsOfActions = new HashMap <Action, Integer>();
		Integer partitionOfCurrentAction = null;
		System.out.println("Computing the Full Partition...");
		int iteration = 1;
		// do {
			oldPartition = newPartition;
			System.out.println("Iteration " + iteration);
			for (CString a : _hmActionName2Action.keySet()) {
				String actionName = a._string;
				if (IGNORE_NOOP && actionName.equals("noop")) {
					continue;
				} else {
					System.out.println("\t- " + a);
					Action action = _hmActionName2Action.get(a);
					Integer partitionOfA = partitionsOfActions.get(action);
					
					if (partitionOfA == null) {
						System.out.println("Computing the partition of " + a);
						partitionOfCurrentAction = partitionDetermining(instanceFluents, action, usefulPartitions);
						partitionOfCurrentAction = getPartitionFromFunction (partitionOfCurrentAction, primeUsed, false);
						// _context.getGraph(partitionOfCurrentAction).launchViewer();
						if (MODEL_MINIMIZATION) {
							// _context.getGraph(partitionOfCurrentAction).launchViewer();
							HashSet leavesBefore = new HashSet();
							HashSet leavesAfter = new HashSet();
							_context.collectLeaves(partitionOfCurrentAction, leavesBefore);
							long numberOfLeavesBefore = leavesBefore.size();
							System.out.println("Leaves before: " + numberOfLeavesBefore);
							
							partitionOfCurrentAction = blockMerge (newPartition, partitionOfCurrentAction, action);
							_context.collectLeaves(partitionOfCurrentAction, leavesAfter);
							long numberOfLeavesAfter = leavesAfter.size();
							System.out.println("Leaves after: " + numberOfLeavesAfter);
							
							System.out.println("...");
							// _context.getGraph(partitionOfCurrentAction).launchViewer();
						}
						
						partitionsOfActions.put(action, partitionOfCurrentAction);
					}
					System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
					if (maxPrimesUsed < countPrimesUsed(primeUsed)) {
						maxPrimesUsed = countPrimesUsed(primeUsed);
					}
						
					newPartition = _context.applyInt (newPartition, partitionOfCurrentAction, ADD.ARITH_PROD);
					// newPartition = getPartitionFromFunction (newPartition, primeUsed, false);
					// _context.getGraph(newPartition).launchViewer();
				}
			}
			
			freeAllPrimes(primeUsed);
			newPartition = getPartitionFromFunction (newPartition, primeUsed, false);
			// System.out.println("Homogeneous partition");
			// _context.getGraph(newPartition).launchViewer();
			iteration++;
		// } while (!oldPartition.equals(newPartition));
			System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
			if (maxPrimesUsed < countPrimesUsed(primeUsed)) {
				maxPrimesUsed = countPrimesUsed(primeUsed);
			}
			
		leaves = new HashSet();
		// System.out.println("|S| = " + cardinalidadeConjuntoDeEstados);
		_context.collectLeaves (newPartition, leaves);
		// System.out.println ("Full Partition computed. Size ? " + leaves.size());
		partitionSize = leaves.size();
		
		// System.out.println("Full Partition");
		// _context.getGraph(newPartition).launchViewer();
		
		stochasticBisimulationTime.setEnd();
		// System.out.println("Tempo Biss. Estoc. = "
		// 		+ cBissEstoc.getIntervalo());
		System.out.println("The maximum number of primes used is: " + maxPrimesUsed);
		System.out.println("Number of times that we needed to recompute primes: " + missingPrimes);
		return newPartition;
	}
	
	/*
	public StringBuffer partitionsInfo() {
		StringBuffer sb = new StringBuffer("");
		sb.append("Partitions information:\n");
		long minNumberOfNodes = Long.MAX_VALUE;
		long minNumberOfLeaves = Long.MAX_VALUE;
		long maxNumberOfNodes = -1;
		long maxNumberOfLeaves = -1;
		double averageNumberOfNodes = 0;
		double averageNumberOfLeaves = 0;
		boolean PRINT_INDIVIDUAL_PARTITION_DATA = false;
		for (Integer partition : allPartitionDDs) {
			HashSet <ADDDNode> leaves = new HashSet <ADDDNode> ();
			long nodes = _context.countExactNodes(partition);
			_context.collectLeaves(partition, leaves);
			if (PRINT_INDIVIDUAL_PARTITION_DATA) {
				sb.append("Partition id: " + partition);
				sb.append("\t Number of Nodes: " + nodes);
				sb.append("\tNumber of Leaves: " + leaves.size());
			}
			
			if (nodes > maxNumberOfNodes) {
				maxNumberOfNodes = nodes;
			}
			
			if (leaves.size() > maxNumberOfLeaves) {
				maxNumberOfLeaves = leaves.size();
			}
			
			if (nodes < minNumberOfNodes) {
				minNumberOfNodes = nodes;
			}
			
			if (leaves.size() < minNumberOfLeaves) {
				minNumberOfLeaves = leaves.size();
			}
			
			averageNumberOfNodes += nodes;
			averageNumberOfLeaves += leaves.size();
		}
		
		averageNumberOfNodes /= allPartitionDDs.size();
		averageNumberOfLeaves /= allPartitionDDs.size();
		
		
		sb.append("Number of MDP ADDs: " + _allMDPADDs.size() + "\n");
		sb.append("Number of partitions: " + allPartitionDDs.size() + "\n");
		sb.append("Average number of nodes in DDs: " + averageNumberOfNodes + "\n");
		sb.append("Average number of leaves in DDs:  " + averageNumberOfLeaves + "\n");
		sb.append("Minimum number of nodes in an ADD: " + minNumberOfNodes + "\n");
		sb.append("Maximum number of nodes in an ADD: " + maxNumberOfNodes + "\n");
		sb.append("Minimum number of leaves in an ADD: " + minNumberOfLeaves + "\n");
		sb.append("Maximum number of leaves in an ADD: " + maxNumberOfLeaves + "\n");
		
		return sb;
	}*/
	
	
	public HashMap <Double, Double> getProbabilityDistribution (HashMap <Double, Double> probabilityDistributionFromI, Double blockI, 
			Integer partitionOfCurrentAction, HashMap <Double, ArrayList<ArrayList <Boolean>>> mapOfBlockToDNF, Action action) {
		// Double probabilityToReachFixedBlock = -1.0d;
		// if (probabilityDistributionFromI != null) {
		//	probabilityToReachFixedBlock = probabilityDistributionFromI.get(fixedBlock);
		// }
		
		
		
		ArrayList <ArrayList<Boolean>> blockDNF = mapOfBlockToDNF.get(blockI);
		ArrayList <Boolean> validAssignment = blockDNF.get(0);
		ArrayList <Boolean> validAssignmentClone = (ArrayList<Boolean>) validAssignment.clone();
		validAssignmentClone.remove(0);
		if (hashOfProbabilityDistribution.get(new Pair(blockI, action)) == null) { 
			int succ = computeSuccesors(validAssignmentClone, action._hmVarID2CPT);
			// _context.getGraph(succ).launchViewer();
			succ = _context.remapGIDsInt (succ, _hmStringPrimeVarID2VarID);
			// _context.getGraph(succ).launchViewer();
			HashMap <Double, Double> probabilityDistribution = new HashMap <Double, Double> ();
			HashMap <ArrayList<Boolean>, Double> probabilityDistributionWithDNF = getAllPaths(succ, false);
			for (ArrayList <Boolean> assignmentInDNF : probabilityDistributionWithDNF.keySet()) {
				Double probability = probabilityDistributionWithDNF.get(assignmentInDNF);
				ArrayList <Boolean> assignmentInDNFClone = (ArrayList<Boolean>) assignmentInDNF.clone();
				assignmentInDNFClone.remove(0);
				Double block = _context.evaluate(partitionOfCurrentAction, assignmentInDNFClone);
				// probabilityDistribution.put(block, probability);
				if (probabilityDistribution.get(block) == null) {
					probabilityDistribution.put(block, probability);
				} else {
					Double oldProbability = probabilityDistribution.get(block);
					probabilityDistribution.put(block, oldProbability + probability);
				}
			}
			// probabilityDistribution = getAllStates(probabilityDistribution)
				
			Pair <Double, CString> stateAction = new Pair <Double, CString> (blockI, action._csActionName); 
			hashOfProbabilityDistribution.put(stateAction, probabilityDistribution);
		}
		probabilityDistributionFromI = 
				hashOfProbabilityDistribution.get(new Pair(blockI, action._csActionName));
		return probabilityDistributionFromI;
		// probabilityToReachFixedBlock = probabilityDistributionFromI.get(fixedBlock);
		// return probabilityToReachFixedBlock;
	}
	
	public HashMap <ArrayList<Boolean>, Double> removeUnreachableStateAssigns (HashMap <ArrayList<Boolean>, Double> blocksAndIdentifiers) {
		HashMap <ArrayList<Boolean>, Double> reachableBlocksAndIdentifiers = (HashMap<ArrayList<Boolean>, Double>) blocksAndIdentifiers.clone();
		for (ArrayList <Boolean> assign : blocksAndIdentifiers.keySet()) {
			if (blocksAndIdentifiers.get(assign) == 0) {
				reachableBlocksAndIdentifiers.remove(assign);
			}
		}
		return reachableBlocksAndIdentifiers;
	}
	
	int vez = 1;
	HashMap <Pair<Double, CString>, HashMap<Double, Double>> hashOfProbabilityDistribution =
			new HashMap <Pair<Double, CString>, HashMap<Double, Double>>();

	public void validateDoublePrecision (Integer partition) {
		HashSet <ADDDNode> leavesOfPartition = new HashSet <ADDDNode>();
		_context.collectLeaves(partition, leavesOfPartition);
		for (ADDDNode leaf : leavesOfPartition) {
			if (Double.isNaN(leaf._dLower) || Double.isInfinite(leaf._dLower)) {
				throw new RuntimeException("Overflow/Underflow");
			}
		}
	}
	
	public Integer getPartitionFromFunction (Integer function, LinkedHashMap <Integer, Boolean> primeMapping, boolean remapZeros) {
		HashMap<Double, Integer> oldValueToPrime = new HashMap <Double, Integer> ();
		reduceRemapLeavesCache = new Hashtable();
		Integer partition = reduceRemapLeaves(function, oldValueToPrime, primeMapping, remapZeros);
		return partition;
	}
	
	private Integer blockMerge (Integer newPartition, Integer partitionOfCurrentAction, Action action) {
		// System.out.println("Partition received");
		// _context.getGraph(partitionOfCurrentAction).launchViewer();
		
		LinkedHashMap<Integer, Boolean> localPrimeUsed = (LinkedHashMap<Integer, Boolean>) primeUsed.clone();
		freeAllPrimes(localPrimeUsed);
		
		HashMap <ArrayList<Boolean>, Double> blocksAndIdentifiers = getAllPaths(partitionOfCurrentAction, false);
		HashMap <Double, ArrayList<ArrayList <Boolean>>> mapBlockIDsToDNF = new HashMap <Double, ArrayList<ArrayList <Boolean>>> ();
		// reduceRemapLeavesCache = new Hashtable();
		for (ArrayList <Boolean> assignment : blocksAndIdentifiers.keySet()) {
			Double assignmentBlockID = blocksAndIdentifiers.get(assignment);
			ArrayList <ArrayList<Boolean>> dnfDescription = mapBlockIDsToDNF.get(assignmentBlockID);
			if (dnfDescription == null) {
				dnfDescription = new ArrayList <ArrayList<Boolean>>();
			}
			dnfDescription.add(assignment);
			mapBlockIDsToDNF.put(assignmentBlockID, dnfDescription);
		}
		
		// blocksAndIdentifiers = removeUnreachableStateAssigns (blocksAndIdentifiers);
		
		// blocksAndIdentifiers = getAllStates (blocksAndIdentifiers);
		ConcurrentLinkedQueue <Double> blocks = new  ConcurrentLinkedQueue <Double> ();
		blocks.addAll(mapBlockIDsToDNF.keySet());
		ArrayList <Double> copyOfBlocks = new ArrayList <Double> (blocks);
		System.out.println("Number of blocks:  " + copyOfBlocks.size());
		// _context.getGraph(partitionOfCurrentAction).launchViewer();
		
		// Para cada bloco e para aï¿½ï¿½o atual, obtem a funï¿½ï¿½o de transiï¿½ï¿½o.
		int validBlockTransitions = 0;
		for (Double block : blocks) {
			HashMap <Double, Double> probabilityDistribution = 
					hashOfProbabilityDistribution.get(new Pair(block, action._csActionName));
			probabilityDistribution = getProbabilityDistribution (probabilityDistribution, block, 
					partitionOfCurrentAction, mapBlockIDsToDNF, action);
			hashOfProbabilityDistribution.put(new Pair(block, action._csActionName), probabilityDistribution);
			double sum = 0.0d;
			for (Double blockJ : probabilityDistribution.keySet()) {
				sum += probabilityDistribution.get(blockJ);
			}
			
			if (Math.abs(sum - 1) < 0.001) {
				validBlockTransitions++;
			}
		}
		
		System.out.println("Valid Block Transitions = " + validBlockTransitions);
		
		// Para cada bloco que pode ser alcanï¿½ado, gere uma partiï¿½ï¿½o distinta e insira a mesma na intersecï¿½ï¿½o.
		Integer partitionIntersection = _context.getConstantNode(1.0d);
		HashMap <Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
		int jCounter = 1;
		for (Double blockJ : blocks) {
			// System.out.println("jCounter = " + jCounter++);
			Integer stableBlocksWRTBlockJ = _context.getConstantNode(0.0d);
			for (Double blockI : blocks) {
				Pair p = new Pair(blockI, action._csActionName);
				HashMap <Double, Double> probabilityDistribution = hashOfProbabilityDistribution.get(p);
				Double probabilityToReachBlockJ = probabilityDistribution.get(blockJ); 
				if (probabilityToReachBlockJ != null) {
					for (ArrayList <Boolean> assignmentInDNF : mapBlockIDsToDNF.get(blockI)) {
						ArrayList <Boolean> assignmentInDNFClone = (ArrayList<Boolean>) assignmentInDNF.clone();
						assignmentInDNFClone.remove(0);
						stableBlocksWRTBlockJ = DDUtils.UpdateValue(_context, stableBlocksWRTBlockJ, assignmentInDNFClone, probabilityToReachBlockJ);
					}
				}
			}
			
			// _context.getGraph(stableBlocksWRTBlockJ).launchViewer();
			
			// Agrupa estados que tem a probabilidade dentro de um epsilon de alcanï¿½ar um bloco de estados.
			if (EPSILON_MODEL_REDUCTION > 0.0d) {
			 	_context.setPrunePrecision (EPSILON_MODEL_REDUCTION);
				stableBlocksWRTBlockJ = _context.pruneNodes (stableBlocksWRTBlockJ);
				// _context.getGraph(stableBlocksWRTBlockJ).launchViewer();
			}
			
			Integer partitionStableWRTBlockJ = getPartitionFromFunction(stableBlocksWRTBlockJ, localPrimeUsed, true);
			partitionIntersection = _context.applyInt(partitionIntersection, partitionStableWRTBlockJ, ADD.ARITH_PROD);
			// validateDoublePrecision(partitionIntersection);
			freeAllPrimes(localPrimeUsed);
			partitionIntersection = getPartitionFromFunction (partitionIntersection, localPrimeUsed, true);
		}
		partitionIntersection = getPartitionFromFunction (partitionIntersection, primeUsed, true);
		
		// System.out.println("Partition returned");
		// _context.getGraph(partitionIntersection).launchViewer();
		// Interseccao
		return partitionIntersection;
		
	}

	private void freeThesePrimes(int partition) {
		HashSet <ADDDNode> usedLeaves = new HashSet <ADDDNode>();
		_context.collectLeaves(partition, usedLeaves);
		for (ADDDNode node : usedLeaves) {
			Integer prime = (int) node._dLower;
			if (primeUsed.get(prime).equals(true)) {
				primeUsed.put(prime, false);
			}
		}
	}

	private HashMap<ArrayList<Boolean>, Double> getAllStates(
			HashMap<ArrayList<Boolean>, Double> probabilityDistribution) {
		HashMap<ArrayList <Boolean>, Double> allStates = new HashMap<ArrayList <Boolean>, Double>();
		for (ArrayList <Boolean> assignment : probabilityDistribution.keySet()) {
			Double assignmentValue = probabilityDistribution.get(assignment);
			for (int i = 1; i < (assignment.size())/2; i++) {
				ArrayList <ArrayList<Boolean>> statesInAssignment = new ArrayList <ArrayList<Boolean>>();
				ArrayList <ArrayList<Boolean>> completeStates = new ArrayList <ArrayList <Boolean>> ();
				statesInAssignment.add(assignment);
				while (!statesInAssignment.isEmpty()) {
					boolean complete = true;
					assignment = statesInAssignment.remove(0);
					for (int j = 1; j < (assignment.size())/2; j++) {
						if (assignment.get(j) == null) {
							complete = false;
							ArrayList <Boolean> assignmentTrue = (ArrayList<Boolean>) assignment.clone();
							ArrayList <Boolean> assignmentFalse = (ArrayList<Boolean>) assignment.clone();
							assignmentTrue.set(j, true);
							assignmentFalse.set(j, false);
							statesInAssignment.add(assignmentTrue);
							statesInAssignment.add(assignmentFalse);
							break;
						}
					}
					
					// System.out.println("add statesInAssignment to allStates...");
					
					if (complete) {
						allStates.put(assignment, assignmentValue);
						while (!statesInAssignment.isEmpty()) {
							ArrayList <Boolean> currentState = statesInAssignment.remove(0);
							allStates.put(currentState, assignmentValue);
						}
					}
				}
			}
		}
		return allStates;
	}

	private void verifyRewardPartition(
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition, int newActionReward) {
		
		HashSet<ArrayList<Boolean>> masterStates = getMasterStates(partition);
		int i = 1;
		
		System.out.println("Epsilon = " + EPSILON_APROXIMATION);
		for (CString a : _hmActionName2Action.keySet()) {
			Action action = _hmActionName2Action.get(a);
			System.out.println("Partition considering action " + a);
			for (ArrayList <Boolean> masterState : masterStates) {
				System.out.println("Block " + i++ + " values = {");
				for (ArrayList <Boolean> state : partition.keySet()) {
					ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
					if (partition.get(state).equals(masterState)) {
						stateClone.remove(0);
						System.out.println(state + " = " + _context.evaluate(newActionReward, stateClone));
					}
				}
				System.out.println("}");
			}
		}
		
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
				// Expande a subÃ¡rvore low
				inOrderSearch (lowNode, assign, alEstadoProb);
				assign.set(level_var, new Boolean(true));
				// Expande a subÃ¡rvore high
				inOrderSearch (highNode, assign, alEstadoProb);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de serem alcanÃ§ados
				if (probabilidade > 0.0d) {
					// Double probanterior = (alEstadoProb.isEmpty()? 0.0d : alEstadoProb.get(0)._dProb);
					ArrayList <Boolean> newAssign = new ArrayList <Boolean>();
					newAssign.addAll(assign);
					ProbState novoNo = new ProbState(probabilidade, newAssign);
					alEstadoProb.add(0, novoNo);
				}
			}
		}
	}
	
	private ArrayList<ProbState> computeSuccesorsEnum(ArrayList state,HashMap<Integer, Integer> iD2ADD) {
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
		inOrderSearch(_context.getNode(multCPTs), assign, alEstadoProb);
		// alEstadoProb.get(0)._dProb = 1;
		// alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		return alEstadoProb;
	}
	

	/**
	 * Modificar para nao utilizar mais ArrayList <ProbState>
	 * 
	 * @param state
	 * @param iD2ADD
	 * @param _csActionName
	 * @return
	 */
	private ArrayList<ProbState> computeSuccessorsProbEnum(ArrayList<Boolean> state, HashMap<Integer, Integer> iD2ADD,
			CString _csActionName, boolean extracting) {
		Integer multCPTs = _context.getConstantNode(1d);
		Integer xiprime;
		
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();

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
		
		optimizedCPTInOrderSearch(_context.getNode(multCPTs), assign, transicoes, extracting);
		
		if (USING_BINARY_SEARCH_SORTITION) {
			for (int i = 1; i < transicoes.size(); i++) {
				double probabilidadeI = transicoes.get(i)._dProb;
				double probabilidadeIAnterior = transicoes.get(i - 1)._dProb;
				transicoes.get(i)._dProb = probabilidadeI + probabilidadeIAnterior;
			}
		}
		
		transicoes.get(transicoes.size() - 1)._dProb = 1.0d;
		
		// System.out.println("Transicao = " + transicoes.get(transicoes.size() - 1)._dProb);

		return transicoes;
	}
	
	public void optimizedCPTInOrderSearch(ADDNode node,	ArrayList<Boolean> assign, ArrayList<ProbState> transicoes,
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
				optimizedCPTInOrderSearch(lowNode, assignFalse, transicoes,
						extracting);

				// Expande a subarvore high
				ArrayList<Boolean> assignTrue = (ArrayList<Boolean>) assign
						.clone();
				assignTrue.set(level_var, new Boolean(true));
				optimizedCPTInOrderSearch(highNode, assignTrue, transicoes,
						extracting);

			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = leaf._dLower;
				// Adiciona apenas os estados com probabilidade maior que de
				// serem alcanÃ§ados
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
					
					double valorBloco = _context.evaluate(stochasticBisimulation, newAssign);
					newAssign.add(0, null);
					

					// Estado sAux = mdp.optimizedEncontreEstadoAtribuicao(newAssign);
					// ArrayList <Boolean> representantAux = mdp.getRepresentant(newAssign);
					ArrayList <Boolean> representantAux = mdp.getRepresentant(valorBloco);
					
					if (representantAux != null) {
						// Transiï¿½ï¿½o para um estado que jï¿½ foi adicionado ao
						// MDP.
						boolean transitionExists = false;
						for (int i = 0; i < transicoes.size(); i++) {
							ProbState t = transicoes.get(i);
							double valorBlocoAlState = getValorBloco (t.nextRepresentant);
							ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
							
							if (alStateRepresentant.equals(representantAux)) {
								t._dProb = t._dProb + probabilidade.floatValue();
								transitionExists = true;
								break;
							}
						}
							
						if (!transitionExists) {
							ProbState t = new ProbState(probabilidade, representantAux);
							transicoes.add(t);
						}
						
						if (valueFunction.get(representantAux) == null) {
							valueFunction.put(representantAux, heuristicaAdmissivel);
							solved.put(representantAux, false);
						}
					} else {
						// Estado seguinte que ainda nï¿½o estï¿½ no MDP.
						if (extracting) {
							HashSet blocos = new HashSet();
							_context.collectLeaves(stochasticBisimulation, blocos);
								
							ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) newAssign.clone();
							stateAssignClone.remove(0);
							if (!hasNulls) {
								valorBloco = _context.evaluate(stochasticBisimulation, stateAssignClone);
								stateAssignClone.add(0, null);
								ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, stateAssignClone);
								ProbState t = new ProbState(probabilidade, representant);
								transicoes.add(t);
								
								if (valueFunction.get(representant) == null) {
									valueFunction.put(representant, heuristicaAdmissivel);
									solved.put(representant, false);
								}
							} else {
								stateAssignClone.add(0, null);
								HashSet <ArrayList <Boolean>> validAssignments = new HashSet <ArrayList <Boolean>>();
								findValidAssignments(assign, validAssignments, (assign.size() / 2) - 1);
								for (ArrayList <Boolean> assignment : validAssignments) {
									ProbState t = null;
									valorBloco = _context.evaluate(stochasticBisimulation, assignment);
									assignment.add(0, null);
									
									ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, assignment);
									boolean transitionExists = false;
									for (int i = 0; i < transicoes.size(); i++) {
										t = transicoes.get(i);
										double valorBlocoAlState = getValorBloco (t.nextRepresentant);
										ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
										if (alStateRepresentant.equals(representant)) {
											t._dProb = t._dProb + probabilidade;
											transitionExists = true;
											break;
										}
									}
										
									if (!transitionExists) {
										t = new ProbState(probabilidade, representant);
										transicoes.add(t);
									}
									
									if (valueFunction.get(representant) == null) {
										valueFunction.put(representant, heuristicaAdmissivel);
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

	private void printPartitonBlockIDs(ArrayList<Integer> partition) {
		for (int i = 0; i < partition.size(); i++) {
			System.out.print("BlockID = " + partition.get(i) + " ");
		}
		System.out.println();
	}

	/*
	private ArrayList<Integer> blockSplit(
			ArrayList<Integer> partitionIntersection, int blockBId,
			int blockCId, LinkedHashSet<Integer> fluentsOfC, Action action) {
		ArrayList<Integer> blockSplitted = new ArrayList<Integer>();
		ArrayList<Integer> blockToPartition = new ArrayList<Integer>();
		blockToPartition.add(blockBId);

		// System.out.println("Bloco a ser dividido: ");
		// _context.getGraph(blockBId).launchViewer();

		// Isso pode ser feito uma vez apenas para cada bloco e nÃ£o para cada
		// aÃ§Ã£o...
		// LinkedHashSet <Integer> fluentsOfC = getFluentsFromBlock (blockCId);
		ArrayList<Integer> pS = partitionDetermining(fluentsOfC, action);

		// System.out.println("PQ");
		// showBDDPartition(pQ);

		blockSplitted = calculateIntersection(blockToPartition, pS);

		// Esse BDD e o equivalente a P_S ^ f_B
		// showBDDPartition(blockSplitted);
		return blockSplitted;
	}*/
	HashSet <Action> actionsVerified = new HashSet <Action> ();
	LinkedList <Double> allLeavesValues = new LinkedList <Double> ();
	
	public void fillAllLeavesValues (Action action, ArrayList <ADDDNode> actionLeaves) {
		if (!actionsVerified.contains(action)) {
			for (ADDDNode node : actionLeaves) {
				allLeavesValues.add (node._dLower);
			}
			actionsVerified.add (action);
		}
	}
	
	public int getLeavesOfTransitionFunction () {
		return allLeavesValues.size();
	}
	
	public Double getLeavesEqualToZero () {
		double zeroCounter = 0;
		for (Double leaveValue : allLeavesValues) {
			if (leaveValue.doubleValue() == 0.0d) {
				zeroCounter++;
			}
		}
		return zeroCounter;
	}

	private Integer partitionDetermining(LinkedHashSet<Integer> fluentsOfC, Action action, ArrayList <Integer> usefulPartitions) {
		
		Integer probabilityIntersection = _context.getConstantNode(1);
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet(
				getNextStateFluents(fluentsOfC));
		 ArrayList <ADDDNode> actionLeaves = new ArrayList <ADDDNode>();
		HashSet <ADDDNode> leaves;
		
		if (SHOW_PARTITION_DETERMINING) {
			System.out.println("Action: " + action._csActionName);
		}
		
		// System.out.println("|X_i'| = " + nextStateFluents.size());
		Iterator<Integer> nextStateFluentsIterator = nextStateFluents
				.iterator();
		int counter = 0;
		while (nextStateFluentsIterator.hasNext()) {
			Integer nextStateFluent = nextStateFluentsIterator.next();
			if (action._hmVarID2CPT.containsKey(nextStateFluent)) {
				leaves = new HashSet <ADDDNode> ();
				HashMap <Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
				Integer head_var_gid = nextStateFluent;
				Integer cpt_dd = action._hmVarID2CPT.get(head_var_gid);
				System.out.println("|X'| = " +  _translation._context._hmID2VarName.get(nextStateFluent));
				if (usefulPartitions.contains(cpt_dd)) {
					// _context.getGraph(cpt_dd).launchViewer();
					_context.collectLeaves(cpt_dd, leaves);
					actionLeaves.addAll(leaves);
					Integer cptDDRestrictedToTrue = _context.restrict(cpt_dd, head_var_gid, ADD.RESTRICT_HIGH);
					// _context.getGraph(cptDDRestrictedToTrue).launchViewer();
					
					Integer newCPTDDRestricted = -1;
					if (EPSILON_APROXIMATION > 0.0d) {
					 	_context.setPrunePrecision (EPSILON_APROXIMATION);
						Integer cpt_dd_compact = _context.pruneNodes (cpt_dd);
						cptDDRestrictedToTrue = _context.restrict(cpt_dd_compact, head_var_gid, ADD.RESTRICT_HIGH);
					}
					
					// _context.getGraph(cptDDRestricted).launchViewer();
					Integer partitionOfFluent = getPartitionFromFunction (cptDDRestrictedToTrue, primeUsed, true);
					
					// _context.getGraph(partitionOfFluent).launchViewer();
					if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
						// _context.getGraph(reachableStates).launchViewer();
						partitionOfFluent = _context.applyInt(partitionOfFluent, reachableStates, ADD.ARITH_PROD);
						// _context.getGraph(partitionOfFluent).launchViewer();
					}
					//_context.getGraph(partitionOfFluent).launchViewer();
					probabilityIntersection = _context.applyInt(probabilityIntersection, partitionOfFluent, DD.ARITH_PROD);
					probabilityIntersection = getPartitionFromFunction (probabilityIntersection, primeUsed, false);
					// _context.getGraph(probabilityIntersection).launchViewer();
					if (ONLY_USEFUL_PARTITIONS) {
						usefulPartitions.remove(cpt_dd);
					}
				}
				counter++;
			}
			
			if (SHOW_PARTITION_DETERMINING) {
				System.out.println("Current partition for the iteration: " + counter);
				System.out.println("Number of nodes " + _context.countExactNodes(probabilityIntersection));
				HashSet <ADDDNode> partitionBlocks = new HashSet <ADDDNode>();
				_context.collectLeaves(probabilityIntersection, partitionBlocks);
				System.out.println("Number of leaves " + partitionBlocks.size());
				// _context.getGraph(probabilityIntersection).launchViewer();
			}
			
		}
		fillAllLeavesValues (action, actionLeaves);
		System.out.println (MemDisplay());
		// _context.getGraph(probabilityIntersection).launchViewer();
		
		return probabilityIntersection;
	}
	
	/**
	 * Receives all partitions of the original MDP and return those that are
	 * useful and ignore the redundant ones.
	 * @param partitions
	 */
	public ArrayList <Integer> identifyAllRedundantPartitions (ArrayList <Integer> partitions) {
		HashMap <Integer, Integer> partitionWORepetitionToSimplerPartition = new HashMap <Integer, Integer>();
		System.out.println ("|All Partitions| = " + _allMDPADDs.size());
		System.out.println("All Partitions = " + partitions);
		ArrayList <Integer> partitionsWithoutRepetition = new ArrayList <Integer> ((new HashSet <Integer> (partitions))); 
		System.out.println("|All Partitions without repetitions| = " + partitionsWithoutRepetition.size());
		System.out.println("All Partitions without repetitions = " + partitionsWithoutRepetition);
		
		
		ArrayList <Integer> simplerPartitions = (ArrayList <Integer>) partitionsWithoutRepetition.clone();
		for (int i = 0; i < simplerPartitions.size(); i++) {
			HashMap <Double, Integer> oldValueToCounting = new HashMap <Double, Integer> ();
			simplifyPartitionCache = new Hashtable();
			// _context.getGraph (simplerPartitions.get(i)).launchViewer();
			simplerPartitions.set(i , simplifyPartition (simplerPartitions.get(i), oldValueToCounting));
			partitionWORepetitionToSimplerPartition.put(partitionsWithoutRepetition.get(i), simplerPartitions.get(i));
			// _context.getGraph (simplerPartitions.get(i)).launchViewer();
		}
		
		for (int i = 0; i < partitionsWithoutRepetition.size(); i++) {
			Integer partitionA = partitionsWithoutRepetition.get(i);
			Integer simplePartitionA = partitionWORepetitionToSimplerPartition.get(partitionA);
			
			if (isADDRedundant.get(partitionA) == null) {
				isADDRedundant.put(partitionA, false);
			} else {
				continue;
			}
			
			for (int j = i + 1; j < partitionsWithoutRepetition.size(); j++) {
				Integer partitionB = partitionsWithoutRepetition.get(j);
				Integer simplePartitionB = partitionWORepetitionToSimplerPartition.get(partitionB);
				
				if (isPartitionAEqualsToPartitionB (simplePartitionA, simplePartitionB)) {
					System.out.println("Partition " + partitionA + " is structully equal to Partition " + partitionB);
					// _context.getGraph(simplePartitionA).launchViewer();
					// _context.getGraph(simplePartitionB).launchViewer();
					// _context.getGraph(partitionA).launchViewer();
					// _context.getGraph(partitionB).launchViewer();
					isADDRedundant.put(partitionB, true);
				}
				
			}
		}
		ArrayList <Integer> usefulPartitions = getUsefulAndRedundantPartitions();
		// System.out.println("All MDP ADDs: " + _allMDPADDs.size());
		// System.out.println("Useful partitions size: " + usefulPartitions.size());
		// System.out.println("Useful partitions: " + usefulPartitions);
		// print the useful partitions
		// for (int i = 0; i < usefulPartitions.size(); i++) {
		//	_context.getGraph(usefulPartitions.get(i)).launchViewer();
		// }
		return usefulPartitions;
	
		
		// return partitionsWithoutRepetition; // enquanto simplificaï¿½ï¿½o nï¿½o funciona...
	}
	
	private Integer simplifyPartition (Integer simplerPartition, HashMap <Double, Integer> oldValueToCounting) {
		Integer Fr = (Integer) simplifyPartitionCache.get(simplerPartition);
    	if (Fr == null) {
    		ADDNode nodeKey = _context.getNode(simplerPartition);
    		if (nodeKey instanceof ADDINode) {
	    		Integer Fh = simplifyPartition(((ADDINode)nodeKey)._nHigh, oldValueToCounting);
	    		Integer Fl = simplifyPartition(((ADDINode)nodeKey)._nLow, oldValueToCounting);
	    		Integer Fvar = ((ADDINode)nodeKey)._nTestVarID;
	    		Fr  =_context.getINode(Fvar, Fl, Fh, true);
	    		simplifyPartitionCache.put(simplerPartition, Fr);
	    	} else {
    			ADDDNode nod = (ADDDNode)nodeKey;
    			// modificar este trecho para inserir nï¿½mero primo.
    			// necessï¿½rio de um contador global de nï¿½meros primos de forma
    			// que sempre que necessï¿½rio, a contagem seja incrementada e seja
    			// garantido que um nï¿½mero primo diferente serï¿½ obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necessï¿½rio alguma regra para nï¿½o separar blocos...
    			if (oldValueToCounting.get(nod._dUpper) == null) {
    				int newValue = oldValueToCounting.size() + 1;
    				oldValueToCounting.put(nod._dUpper, newValue);
    				return _context.getConstantNode(newValue);
    			} else {
    				return _context.getConstantNode(oldValueToCounting.get(nod._dUpper));
    			}
    		}
    	}
    	return Fr;
	}

	/**
	 * Show useful and redundant partitions
	 */
	public ArrayList <Integer> getUsefulAndRedundantPartitions() {
		ArrayList <Integer> usefulPartitions = new ArrayList <Integer> ();
		ArrayList <Integer> redundantPartitions = new ArrayList <Integer> ();
		for (Integer partition : isADDRedundant.keySet()) {
			if (isADDRedundant.get(partition).booleanValue() == false) {
				usefulPartitions.add(partition);
			} else {
				redundantPartitions.add(partition);
			}
		}
		
		// System.out.println("Useful partitions: " + usefulPartitions);
		// System.out.println("Redundant partitions: " + redundantPartitions);
		return usefulPartitions;
	}
	
	
	/**
	 * Determines if partition A represented as an ADD is equal to the
	 * partition B represented as another ADD.
	 * @param A
	 * @param B
	 * @return
	 */
	public boolean isPartitionAEqualsToPartitionB (Integer A, Integer B) {
		return A.equals(B);
	}

	private LinkedHashSet<Integer> getNextStateFluents(
			LinkedHashSet<Integer> fluentsOfC) {
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet<Integer>();
		Iterator<Integer> iterator = fluentsOfC.iterator();
		while (iterator.hasNext()) {
			Integer gid = iterator.next();
			String varName = (String) _context._hmID2VarName.get(gid);
			varName = varName + "'";
			Integer nextStateGid = (Integer) _context._hmVarName2ID
					.get(varName);
			nextStateFluents.add(nextStateGid);
		}
		return nextStateFluents;
	}

	/**
	 * Also known as S-SPLIT.
	 * 
	 * @param blockBId
	 * @param blockCId
	 * @param partitionIntersection
	 */
	/*
	private ArrayList<Integer> structuredSplit(int blockBId, int blockCId,
			ArrayList<Integer> partitionIntersection,
			HashSet<Integer> ignoredBlocks) {
		
		ArrayList<Integer> newPartition = (ArrayList<Integer>) partitionIntersection.clone();
		int oldBBlockId = -1;
		
		for (int i = 0; i < newPartition.size(); i++) {
			if (newPartition.get(i).intValue() == blockBId) {
				// System.out.println("Block B (Id: " + blockBId +
				// ") removed.");
				oldBBlockId = blockBId;
				newPartition.remove(i);
				break;
			}
		}

		// define uma nova particao a partir de B, o bloco a ser refinado.
		int bPartitioning = blockBId;
		ArrayList<Integer> bSubBlocks = new ArrayList<Integer>();
		ArrayList<Integer> intersectionOfBSubBlocks = new ArrayList<Integer>();
		bSubBlocks.add(bPartitioning);
		intersectionOfBSubBlocks.add(bPartitioning);

		boolean hasAllFluents = true;
		// System.out.println("Block to be partitioned: " + blockBId);
		// showBDDPartition(bSubBlocks);
		
		if (blockStable.get(blockBId) == null) {
			HashMap <ArrayList <Boolean>, Double> bMembers = getTruthAssignments(blockBId);
			if (bMembers.size() == 1) {
				for (ArrayList <Boolean> member : bMembers.keySet()) {
					System.out.println(member);
					for (int i = 1; i < member.size(); i++) {
						if (member.get(i) == null) {
							hasAllFluents = false; // block can be splitted
						}
					}
				}
			} else {
				hasAllFluents = false;
			}
			blockStable.put(blockBId, hasAllFluents);
		} else {
			hasAllFluents = blockStable.get(blockBId);
		}

		// System.out.println("Searching stability w.r.t.: " + blockCId);
		// _context.getGraph(blockCId).launchViewer();
		
		

		LinkedHashSet<Integer> fluentsOfC = getFluentsFromBlock(blockCId);

		// if (truthAssignments.size() >= 1) {
		if (!hasAllFluents) {
			for (CString a : _hmActionName2Action.keySet()) {
				// System.out.println("\t- " + a);
				Action action = _hmActionName2Action.get(a);
				ArrayList<Integer> possibleSubBlocks = blockSplit(
						partitionIntersection, blockBId, blockCId, fluentsOfC,
						action);
						// System.out.println("Block-split result: " + possibleSubBlocks);
				// showBDDPartition(possibleSubBlocks);
						// optimal Structured Split needs to coarsen the subBlocks here...
				// this step can take exponential time
				if (S_SPLIT == OTIMO) {
					possibleSubBlocks = optimalSplitCoarsening(possibleSubBlocks, blockCId, fluentsOfC, action);
				} else {
					if (EPSILON_APROXIMATION > 0.0d) {
						S_SPLIT = OTIMO;
						possibleSubBlocks = optimalSplitCoarsening(possibleSubBlocks, blockCId, fluentsOfC, action);
					}
				}
				// System.out.println("Optimal split partition computed: " +
				// possibleSubBlocks);
				// showBDDPartition(possibleSubBlocks);
				intersectionOfBSubBlocks = calculateIntersection(
						intersectionOfBSubBlocks, possibleSubBlocks);
				// System.out.println("Intersection: ");
				// showBDDPartition(intersectionOfBSubBlocks);
			}
		}
		
		// remove the 'blank' blocks when intersection size is greater than one
		if (intersectionOfBSubBlocks.size() > 1) {
			for (int i = 0; i < intersectionOfBSubBlocks.size(); i++) {
				int block = intersectionOfBSubBlocks.get(i);
				if (_context.countExactNodes(block) == 1) {
					intersectionOfBSubBlocks.remove(i);
					i = 0;
				}
			}
		}
		
		// System.out.println("Intersection of bSubBlocks:");
		// showBDDPartition(intersectionOfBSubBlocks);
		
		newPartition.addAll(intersectionOfBSubBlocks); // antiga atribuicao
		ignoredBlocks.addAll(intersectionOfBSubBlocks);
		return newPartition; // antigo retorno
		// return intersectionOfBSubBlocks;
	}*/

	public ArrayList<Boolean> getAnyCoherentAssignement(
			ArrayList<Boolean> assignment) {
		ArrayList<Boolean> newAssignment = new ArrayList<Boolean>();
		for (int i = 0; i < assignment.size(); i++) {
			if (assignment.get(i) != null) {
				newAssignment.add(i, assignment.get(i));
			} else {
				newAssignment.add(i, false);
			}
		}

		return newAssignment;
	}
	
 

	/**
	 * A partir de um particionamento nï¿½o-ï¿½timo de B (sem explorar
	 * coincidï¿½ncias). Este mï¿½todo devolve uma partiï¿½ï¿½o mais grosseira se
	 * possï¿½vel.
	 * 
	 * @param possibleBSubBlocks
	 * @param blockCId
	 * @param fluentsOfC
	 * @param action
	 * @param epsilonAproximation
	 * @return
	 */
	private ArrayList<Integer> optimalSplitCoarsening(
			ArrayList<Integer> possibleBSubBlocks, int blockCId,
			LinkedHashSet<Integer> fluentsOfC, Action action) {

		@SuppressWarnings({ "rawtypes", "unchecked" })
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet(
				getNextStateFluents(fluentsOfC));

		Iterator<Integer> nextStateFluentsIterator;

		HashMap<Integer, Double> probabilityReachCFromB = new HashMap<Integer, Double>();

		LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> fluentwisePartition = new LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>>();

		ArrayList<Boolean> assignment = new ArrayList<Boolean>();
		for (int i = 0; i <= _translation._alStateVars.size(); i++) {
			assignment.add(null);
		}
		
		ArrayList<Integer> fluentewisePartitionBDDs = null;
		if (fluentwisePartitionsUsed.get(fluentsOfC) == null) {
			if (fluentsOfC.size() >= 11) {
				System.out.println("|Vars(f_C)| = " + fluentsOfC.size());
			}
			getFluentwisePartition(fluentwisePartition, assignment, new ArrayList<Integer>(fluentsOfC));
			fluentewisePartitionBDDs = partitionAsBDDs(fluentwisePartition);
			fluentwisePartitionsUsed.put(fluentsOfC, fluentewisePartitionBDDs);
		} else {
			fluentewisePartitionBDDs =  fluentwisePartitionsUsed.get(fluentsOfC);
		}

		ArrayList<Integer> originalCPartition = new ArrayList<Integer>();
		originalCPartition.add(blockCId);
		ArrayList<Integer> cSubBlocksConsistentsWithC = calculateIntersection(
				originalCPartition, fluentewisePartitionBDDs);
		
		// System.out.println("Fluentwise partition consistent with C computed.");

		HashMap<ArrayList<Boolean>, Double> truthAssignmentsInC = new HashMap<ArrayList<Boolean>, Double>();
		for (Integer cSubBlock : cSubBlocksConsistentsWithC) {
			truthAssignmentsInC.putAll(getTruthAssignments(cSubBlock));
		}

		for (int blockIndex = 0; blockIndex < possibleBSubBlocks.size(); blockIndex++) {
			Double sum = 0.0;
			Double jointProbability = 1.0;

			int block = possibleBSubBlocks.get(blockIndex);
			// _context.getGraph(block).launchViewer();
			if (_context.countExactNodes(block) != 1) {
				for (ArrayList<Boolean> cAssignment : truthAssignmentsInC.keySet()) {
					// System.out.println("An assignment in C: " + cAssignment);
					HashMap<ArrayList<Boolean>, Double> assignments = getTruthAssignments(block);
	
					Iterator<ArrayList<Boolean>> bIterator = assignments.keySet().iterator();
					ArrayList<Boolean> bAssignment = bIterator.next();
	
					jointProbability = 1.0;
					bAssignment.remove(0);
					// System.out.println("b_i assignment: " + bAssignment);
					// ArrayList <Boolean> consistentBAssignment =
					// getAnyCoherentAssignement(bAssignment);
					// System.out.println("consistent BAssignment: " +
					// consistentBAssignment);
					nextStateFluentsIterator = nextStateFluents.iterator();
					Double probNextFluentTrue = 0.0;
					Double probNextFluentFalse = 0.0;
	
					while (nextStateFluentsIterator.hasNext()) {
						Integer nextStateFluent = nextStateFluentsIterator.next();
						Integer currentStateFluent = nextStateFluent
								- (_context._alOrder.size() / 2);
						if (action._hmVarID2CPT.containsKey(nextStateFluent)) {
							Integer head_var_gid = nextStateFluent;
							Integer cpt_dd = action._hmVarID2CPT.get(head_var_gid);
	
							// multiplica fluente de acordo com a probabilidade de
							// alcanï¿½ar C;
							if (cAssignment.get(currentStateFluent) != null) {
								if (cAssignment.get(currentStateFluent)
										.booleanValue() == true) {
									Integer cptDDRestricted = _context
											.restrict(cpt_dd, head_var_gid,
													ADD.RESTRICT_HIGH);
									// _context.getGraph(cptDDRestricted).launchViewer();
									probNextFluentTrue = _context.evaluate(
											cptDDRestricted, bAssignment);
									jointProbability *= probNextFluentTrue;
								} else {
									Integer cptDDRestricted = _context.restrict(
											cpt_dd, head_var_gid, ADD.RESTRICT_LOW);
									// _context.getGraph(cptDDRestricted).launchViewer();
									probNextFluentFalse = _context.evaluate(
											cptDDRestricted, bAssignment);
									jointProbability *= probNextFluentFalse;
								}
							}
						}
					}
					// System.out.println("Joint probability: " + jointProbability);
					sum += jointProbability;
				}
			}
			// System.out.println("Sum = " + sum);
			probabilityReachCFromB.put(block, sum);
		}

		HashSet<Integer> coarsestPossibleSubBlocks = new HashSet<Integer>();
		HashMap<Integer, Boolean> blockIsAggregated = new HashMap<Integer, Boolean>();
		ArrayList<Integer> bMembers = null;

		for (Integer blockB : probabilityReachCFromB.keySet()) {
			Integer newBlockBDD = -1;
			if (blockIsAggregated.get(blockB) == null) {
				blockIsAggregated.put(blockB, true);
				bMembers = new ArrayList<Integer>();
				for (Integer blockC : probabilityReachCFromB.keySet()) {
					if (blockB.intValue() != blockC.intValue()) {
						if (blockIsAggregated.get(blockC) == null) {
							Double probabilityFromB = probabilityReachCFromB
									.get(blockB);
							Double probabilityFromC = probabilityReachCFromB
									.get(blockC);
							if (Math.abs(probabilityFromB.doubleValue()
									- probabilityFromC.doubleValue()) <= EPSILON_APROXIMATION + 0.000000001) {
								boolean aggregate = true;
								for (Integer bMember : bMembers) {
									Double probabilityFromBMember = probabilityReachCFromB
											.get(bMember);
									if (Math.abs(probabilityFromBMember
											.doubleValue()
											- probabilityFromC.doubleValue()) > EPSILON_APROXIMATION + 0.000000001) {
										aggregate = false;
										break;
									}
								}

								if (aggregate) {
									newBlockBDD = _context.applyInt(blockB,
											blockC, ADD.LOG_OR);
									coarsestPossibleSubBlocks.add(newBlockBDD);
									blockIsAggregated.put(blockC, true);
									bMembers.add(blockC);
								}
							}
						}
					}
				}

				// It wasn't possible to find any 'similar' block.
				if (newBlockBDD == -1) {
					coarsestPossibleSubBlocks.add(blockB);
				}
			}
		}

		@SuppressWarnings({ "unchecked", "rawtypes" })
		ArrayList<Integer> optimalSubBlocks = new ArrayList(
				coarsestPossibleSubBlocks);

		return optimalSubBlocks;
	}

	private void getFluentwisePartition(
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> fluentwisePartition,
			ArrayList<Boolean> assignment, ArrayList<Integer> fluents) {
		if (fluents.size() == 0) {
			fluentwisePartition.put(assignment, assignment);
		} else {
			ArrayList<Integer> tempFluentsTrue = (ArrayList<Integer>) fluents
					.clone();
			ArrayList<Integer> tempFluentsFalse = (ArrayList<Integer>) fluents
					.clone();
			Integer currentFluentTrue = tempFluentsTrue.remove(0);
			Integer currentFluentFalse = tempFluentsFalse.remove(0);

			ArrayList<Boolean> fluentFalseAssignment = (ArrayList<Boolean>) assignment
					.clone();
			fluentFalseAssignment.set(currentFluentFalse, false);
			getFluentwisePartition(fluentwisePartition, fluentFalseAssignment,
					tempFluentsFalse);

			ArrayList<Boolean> fluentTrueAssignment = (ArrayList<Boolean>) assignment
					.clone();
			fluentTrueAssignment.set(currentFluentTrue, true);
			getFluentwisePartition(fluentwisePartition, fluentTrueAssignment,
					tempFluentsTrue);

		}
	}

	/**
	 * For each block of the partition, show the BDD representing the block.
	 * 
	 * @param partition
	 */
	public void showBDDPartition(ArrayList<Integer> partition) {
		for (int i = 0; i < partition.size(); i++) {
			_context.getGraph(partition.get(i)).launchViewer();
		}
	}

	/**
	 * Receives a forest representation of the space state set partition and
	 * print this partition starting by the block master states and then
	 * printing the other states in the block.
	 * 
	 * @param partition
	 */
	public void printForestPartition(
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition) {
		System.out.println("Particionamento: ");

		HashSet<ArrayList<Boolean>> mastersInPartition = getMasterStates(partition);

		for (ArrayList<Boolean> representante : mastersInPartition) {
			System.out.print(representante + " => ");
			for (ArrayList<Boolean> otherStates : getStatesFromBlock(
					representante, partition)) {
				System.out.print(otherStates + " ");
			}
			System.out.println();
		}
	}

	public StringBuffer getForestPartitionAsString(LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> partition) {
		StringBuffer partitionAsString = new StringBuffer();

		HashSet<ArrayList<Boolean>> mastersInPartition = getMasterStates(partition);

		int i = 0;
		for (ArrayList<Boolean> representante : mastersInPartition) {
			partitionAsString.append("s" + i++ + "\n");
			for (ArrayList<Boolean> otherStates : getStatesFromBlock(
					representante, partition)) {
				partitionAsString.append(otherStates +"\n");
			}
		}
		return partitionAsString;
	}
	
	/**
	 * Given a block id from one partition, returns the fluents' ids that appear
	 * in the block description.
	 * 
	 * @param blockID
	 * @return
	 */
	public LinkedHashSet<Integer> getFluentsFromBlock(int blockID) {
		LinkedHashSet<Integer> fluents = new LinkedHashSet<Integer>();
		long numberOfNodes = _context.countExactNodes(blockID);
		fluents.addAll(_context.getGIDs(blockID));

		// Test print #1
		// System.out.println("Fluents: ");
		// for (Integer id : fluents) {
		// System.out.print(_context._hmID2VarName.get(id) + " ");
		// }
		// System.out.println();

		return fluents;
	}

	/**
	 * Receives a partition represented as a forest of trees and return a list
	 * of BDDs' ids which also represent a partition. But using this BDDs, the
	 * computing can be cheaper.
	 * 
	 * @param p
	 * @return
	 */
	public ArrayList<Integer> partitionAsBDDs(
			LinkedHashMap<ArrayList<Boolean>, ArrayList<Boolean>> p) {
		ArrayList<Integer> partitionAsBDDs = new ArrayList<Integer>();
		HashSet<ArrayList<Boolean>> masterStatesInP = getMasterStates(p);
		int blockBDD = -1;
		int statePath = -1;

		for (ArrayList<Boolean> masterState : masterStatesInP) {
			blockBDD = _context.getBNode(false, true);
			HashSet<ArrayList<Boolean>> statesFromCurrentBlock = getStatesFromBlock(
					masterState, p);
			// System.out.println("master state: " + masterState);
			for (ArrayList<Boolean> state : statesFromCurrentBlock) {
				statePath = _context.getBNode(true, true);
				for (int i = 1; i < state.size(); i++) {
					int varID = i;
					String varName = (String) _context._hmID2VarName.get(varID);
					Integer high = null;
					Integer low = null;
					if (state.get(varID) != null) {
						// System.out.print(varName + "=" + state.get(varID) +
						// " ");
						if (state.get(varID).booleanValue() == true) {
							high = _context.getBNode(true, true);
							low = _context.getBNode(false, true);
						} else {
							high = _context.getBNode(false, true);
							low = _context.getBNode(true, true);
						}
					} else {
						continue;
					}
					int gid = ((Integer) _context._hmVarName2ID.get(varName))
							.intValue();
					Integer varNode = _context.getINode(gid, low, high, true);
					statePath = _context.applyInt(statePath, varNode,
							ADD.LOG_AND);
				}
				// print test #1
				// System.out.println("Printing blockBDD: ");
				// _context.getGraph(statePath).launchViewer();
				blockBDD = _context.applyInt(blockBDD, statePath, ADD.LOG_OR);
			}
			// System.out.println();
			if (_context.countExactNodes(blockBDD) > 1) {
				partitionAsBDDs.add(new Integer(blockBDD));
				// System.out.println("Printing blockBDD (" +
				// _context.countExactNodes(blockBDD) + "): ");
				// _context.getGraph(blockBDD).launchViewer();
			}
		}

		if (partitionAsBDDs.size() == 0) {
			partitionAsBDDs.add(_context.getBNode(true, true));
		}

		return partitionAsBDDs;
	}

	/**
	 * Receives two partitions (represented as two list of BDDs' ids) and
	 * calculate the intersection (represented as another partition).
	 * 
	 * @param partitionP1
	 * @param partitionP2
	 * @return
	 */
	public ArrayList<Integer> calculateIntersection(
			ArrayList<Integer> partitionP1, ArrayList<Integer> partitionP2) {
		ArrayList<Integer> partitionIntersection = new ArrayList<Integer>();

		if ((partitionP1.size() == 0) || (partitionP2.size() == 0)) {
			if ((partitionP1.size() == 0) && (partitionP2.size() != 0)) {
				return partitionP2;
			} else if ((partitionP1.size() != 0) && (partitionP2.size() == 0)) {
				return partitionP1;
			} else {
				return partitionP1;
			}
		}

		for (int i = 0; i < partitionP1.size(); i++) {
			int p1BlockGID = partitionP1.get(i);
			// _context.getGraph(p1BlockGID).launchViewer();
			for (int j = 0; j < partitionP2.size(); j++) {
				int p2BlockGID = partitionP2.get(j);
				// _context.getGraph(p2BlockGID).launchViewer();
				int blockIntersection = _context.applyInt(p1BlockGID,
						p2BlockGID, ADD.LOG_AND);
				if (blockIntersection != -1) {
					long numberOfNodes = _context
							.countExactNodes(blockIntersection);
					if (numberOfNodes >= 1) { // necessï¿½rio incluir 1 para gerar partiï¿½ï¿½es unitï¿½rias. 
						if (!partitionIntersection.contains(blockIntersection)) {
							partitionIntersection.add(blockIntersection);
							// _context.getGraph(blockIntersection).launchViewer();
						}
					}
				}
			}
		}

		return partitionIntersection;
	}
	
	public void timeInfo (Cronometro tviTime, double reward) {
		StringBuffer timeInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (timeInfoContent);
		timeInfoContent.append("INSTANCE=" + _sInstanceName + "\n");
		timeInfoContent.append("PLANNER_TIME=" + ((double) lrtdpTime.getTotalMilisegundos() / 1000.0d) + "\n");
		timeInfoContent.append("REWARD=" + reward + "\n");
		// timeInfoContent.append("V*(s0)=" + _valueDD.get(initialState) + "\n");
		geradorDeArquivo.geraArquivo("TVITime/" + _sInstanceName + "_Time.txt");
	}

	public void roundEnd(double reward) {
		timeInfo(tviTime, reward);
		/*
		
		// System.out.println("Imprecisao 2 (Qualidade):" + ((reward - lowerBound40) / (upperBound40 - lowerBound40)));
		
		System.out
				.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out
				.println("*********************************************************");

		clearEverything();
		*/
	}

	private void clearEverything() {
		// TODO Auto-generated method stub
		_context.clearSpecialNodes();
		// while (true) {
		//	if ((RUNTIME.freeMemory() / (1024 * 1024)) < 1024) {
		//		System.out.println("Total Memory: " + (RUNTIME.totalMemory() / (1024 * 1024)));
		//		_context.flushCaches(true);
		//		break;
		//	}
		// }
	}

	public void sessionEnd(double total_reward) {
		System.out
				.println("\n*********************************************************");
		System.out.println(">>> SESSION END, total reward = " + total_reward);
		System.out
				.println("*********************************************************");
	}
	
	

	// Initialize all variables (call before starting value iteration)
	public void resetSolver() {
		_prevDD = _maxDD = -1;
		_valueDD = _context.getConstantNode(0d); // Initialize to 0
		_nIter = -1;
		_sRegrAction = null;
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
			_hmStringPrimeVarID2VarID.put (var_prime, var);
			_hmStringPrimeVarID2VarID.put (var, var_prime);
			_hmNextVarID2VarID.put(var_prime, var);
			_hmNextVarID2VarID.put(var, var);
		}

		_hmAct2Regr = null;
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
		return "Used Memory: " + (total - free) + " MB / Total Memory: " + total + " MB ";
	}

	/**
	 * Ajusta o limite de tempo dado ao simulador.
	 */
	public void setLimitTime(Integer time) {
		AGGREGATION_TIME_LIMIT = time;
	}

}
