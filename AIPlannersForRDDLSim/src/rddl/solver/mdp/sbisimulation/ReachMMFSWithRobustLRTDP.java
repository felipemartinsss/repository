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

package rddl.solver.mdp.sbisimulation;

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
import util.Transicao;
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
import rddl.translate.RDDL2Format;
import util.CString;
import util.Cronometro;
import util.GeradorDeArquivo;
import util.Pair;
import util.ProblemDescription;
import util.SieveOfEratosthenes;
import util.ValueFunctionComparisonsTest;

public class ReachMMFSWithRobustLRTDP extends Policy {
	private static boolean ONLY_REACHABILITY_ANALYSIS = false;
	private static boolean ONLY_BISIMULATION = false;
	// private static boolean DEBUG = true;
	// private static boolean INTERRUPTION = false;
	// private static boolean GENERATE_PARTITION_FILE = false;
	private static boolean MODEL_MINIMIZATION = true;
	private static boolean BISIMULATION_INFO = true;
	private static boolean BISIMULATION_WITH_REACHABILITY_ANALYSIS = true;
	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;
	private static boolean USING_BINARY_SEARCH_SORTITION = false;
	private static int LRTDP = 1;
	private static int PLANEJADOR = LRTDP;

	private static int MINUTE = 60;
	private static int HOUR = 60 * MINUTE;
	private static int DAY = 24 * HOUR; 

	private static int AGGREGATION_TIME_LIMIT = 2 * DAY; // Solver time limit
	private static int OFFLINE_SOLVER_TIME_LIMIT = (int) (90 * DAY); // seconds for one OFFLINE getAction
	private static int ONLINE_SOLVER_TIME_LIMIT = 10; // seconds for one ONLINE getAction
	private static boolean ONLY_USEFUL_PARTITIONS = false; // N�o pode ser true se MODEL_MINIMIZATION = true.
	
	private static int OFFLINE = 0;
	private static int ONLINE = 1;
	private static int PLANEJAMENTO = OFFLINE;
	
	private static int NAO_OTIMO = 0;
	private static int OTIMO = 1;
	
	// Par�metro utilizado para permitir agrega��es de estados 'aproximadamente
	// iguais => epsilon \in [0,1]
	private boolean EPSILON_IN_SPLIT = false;
	private double EPSILON_MODEL_REDUCTION = 0.0d; // use 0.05 for the example_approx_givan
	private boolean EPSILON_FOR_REWARD_PARTITIONS = true;
	
	// Par�metro utilizado para verificar a converg�ncia do algoritmo LRTDP.
	private double bellmanError = 0.001d; // 10^(-3)
	
	private boolean IGNORE_NOOP = false;
	
	// Se for APROXIMATION_IN_REWARD = false, teremos EPSILON = 0 para a fun��o recompensa.
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
	private LinkedHashMap <ArrayList <Boolean>, Double> valueFunction;
	// private HashMap <ArrayList <Boolean>, Float> previousValueFunction;
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
	HashMap <ArrayList <Boolean>, ActionIntervalTransition> pi = null;
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

	// Constructors
	public ReachMMFSWithRobustLRTDP() {
	}

	public ReachMMFSWithRobustLRTDP(
			String instance_name) {
		super(instance_name);
	}
	
	public static class ProbState implements Comparable{
		public double  _dProb;
		public ArrayList<Boolean> nextRepresentant;
		public ProbState(double Prob, ArrayList<Boolean> State) {
			_dProb = Prob;
			nextRepresentant = State;
		}
		public String toString(){
			return "" + _dProb + " = " + nextRepresentant.toString();
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
	
	public class IntervalProbState implements Comparable{
		public double  _dLowerProb;
		public double _dUpperProb;
		public ArrayList<Boolean> nextRepresentant;
		public IntervalProbState(double lowerProb, double upperProb, ArrayList<Boolean> State) {
			_dLowerProb = lowerProb;
			_dUpperProb = upperProb;
			nextRepresentant = State;
		}
		public String toString(){
			return "[" + _dLowerProb + ", " + _dUpperProb + "] = " + nextRepresentant;
		} 

		public boolean equals( Object objeto ) {
			if (objeto == null || !(objeto instanceof IntervalProbState) || !(objeto instanceof Double)) return false;
			double probInferiorCompara = (objeto instanceof IntervalProbState? ((IntervalProbState)objeto)._dLowerProb: (Double)objeto);
			double probSuperiorCompara = (objeto instanceof IntervalProbState? ((IntervalProbState)objeto)._dUpperProb: (Double)objeto);
			return (probInferiorCompara == _dLowerProb) && (probSuperiorCompara == _dUpperProb);
		} 

		public int hashCode() {
			return ((Double)_dLowerProb).hashCode() + ((Double)_dUpperProb).hashCode();
		} 

		public int compareTo( Object objeto ) {
			if (objeto instanceof IntervalProbState) {
				IntervalProbState outraTransicao = (IntervalProbState) objeto;
				if (valueFunction != null) {
					Double thisValue = new Double(valueFunction.get(this.nextRepresentant));
					Double thatValue = new Double(valueFunction.get(outraTransicao.nextRepresentant));
					return thisValue.compareTo(thatValue);
				} else {
					return -1;
				}
			} else {
				return -1;
			}
		}
	}

	HashMap <Double, ArrayList<ArrayList <Boolean>>> mapBlockIDsToDNF = null;
	HashMap <CString, Integer> bmdpJointProbabilities = new HashMap <CString, Integer>();
	HashMap <Double, Integer> mapBlockIDToBDD = new HashMap <Double, Integer>();
	private boolean GET_NUMBER_OF_REACHABLE_STATES = true;

	// /////////////////////////////////////////////////////////////////////////
	// Main Action Selection Method
	// ////////////////////////////////////////////////////////////////////////
	@SuppressWarnings("rawtypes")
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {

		if (getActionCounter == 0) {
			getActionTimer = new Cronometro();
			getActionTimer.setStart();
			// previousValueFunction = new HashMap <ArrayList <Boolean>, Float> ();
			valueFunction = new LinkedHashMap <ArrayList <Boolean>, Double> ();
			solved = new HashMap <ArrayList <Boolean>, Boolean>();
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
			try {
				if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
					reachabilityTime.setStart();
					reachableStates = findReachableStates ((ArrayList <Boolean>) add_state_assign_clone, 40);
					reachabilityTime.setEnd();
				}
				
				// if (ONLY_REACHABILITY_ANALYSIS) {
				//	System.out.println("Only Reachability Analysis have been done.");
				// 	System.exit(0);
				// }
				if (GET_NUMBER_OF_REACHABLE_STATES ) {
					reachableStatesSize = getReachableStatesSize(reachableStates);
					System.out.println("reachable states = " + reachableStatesSize);
				}
				
				stochasticBisimulationTime.setStart();
				stochasticBisimulation = getReducedExplicitMDP(AGGREGATION_TIME_LIMIT);
				stochasticBisimulationTime.setEnd();
				
				// _context.getGraph(stochasticBisimulation).launchViewer();
				HashMap <ArrayList<Boolean>, Double> blocksAndIdentifiers = getAllPaths(stochasticBisimulation, false);
				mapBlockIDsToDNF = new HashMap <Double, ArrayList<ArrayList <Boolean>>> ();
				// reduceRemapLeavesCache = new Hashtable();
				for (ArrayList <Boolean> assignment : blocksAndIdentifiers.keySet()) {
					Double assignmentBlockID = blocksAndIdentifiers.get(assignment);
					ArrayList <ArrayList<Boolean>> dnfDescription = mapBlockIDsToDNF.get(assignmentBlockID);
					if (dnfDescription == null) {
						dnfDescription = new ArrayList <ArrayList<Boolean>>();
					}
					dnfDescription.add(assignment);
					mapBlockIDsToDNF.put(assignmentBlockID, dnfDescription);
					Integer blockDescription = mapBlockIDToBDD.get(assignmentBlockID);
					if (blockDescription == null) {
						blockDescription = _context.getConstantNode(0.0d);
					}
					ArrayList <Boolean> exprFromIClone = (ArrayList<Boolean>) assignment.clone();
					exprFromIClone.remove(0);
					blockDescription = DDUtils.UpdateValue(_context, blockDescription, exprFromIClone, 1.0d);
					mapBlockIDToBDD.put(assignmentBlockID, blockDescription);
					
				}
			} catch (TimeOutException toe) {
				System.out.println(toe.getMessage());
			}
			
			if (BISIMULATION_INFO) {
				bisimulationInfo (stochasticBisimulation, stochasticBisimulationTime);
			}
		}

		ArrayList <Boolean> currentAbstractState = mdp.getRepresentant (stateAssign);

		if (currentAbstractState == null) {
			HashSet <ADDDNode> blocos = new HashSet <ADDDNode> ();
			_context.collectLeaves(stochasticBisimulation, blocos);
			ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) stateAssign.clone();
			stateAssignClone.remove(0);
			double valorBloco = _context.evaluate(stochasticBisimulation, stateAssignClone);
			stateAssignClone.add(0, null);
			ArrayList <Boolean> blockRepresentant =  (ArrayList<Boolean>) mapBlockIDsToDNF.get(valorBloco).get(0).clone();
			currentAbstractState = mdp.setRepresentant(valorBloco, stateAssignClone);
				
			if (getActionCounter == 0) {
				// allAssignmentsStochasticBisimulation = getAllPaths(stochasticBisimulation, false);
				// System.out.println("Get All Paths executada para " +  _context._hmID2VarName.size() / 2 + " variaveis.");
				HashSet blocosBissimulacao = new HashSet ();
				_context.collectLeaves(stochasticBisimulation, blocosBissimulacao);
				System.out.println("Number of blocks in the stochastic bisimulation: " + blocosBissimulacao.size());
				STOCHASTIC_BISIMULATION_COMPUTED = true;
				primeNumbers.clear();
				primeNumbers = null;
				soe.suggestToFreeMemory();
				flushCaches();
			}
			
			if (valueFunction.get(stateAssignClone) == null && solved.get(stateAssignClone) == null) {
				valueFunction.put(stateAssignClone, heuristicaAdmissivel);
				solved.put(stateAssignClone, false);
			}
		}		

		_lStartTime = System.currentTimeMillis();
		

		if (getActionCounter == 0) {
			if (ONLY_BISIMULATION) {
				System.out.println("Only bisimulation...");
			} else if (ONLY_REACHABILITY_ANALYSIS) {
				System.out.println("Only reachability analysis...");
			} else {
				if (PLANEJADOR == LRTDP) {
					try {
						// pi = Resolvedor.rtdp(mdp, 0.0001f, pi);
						// Executa LRTDP at� convergir e apenas no primeiro trial.
						if (PLANEJAMENTO == OFFLINE && getActionCounter == 0) {
							_nTimeLimitSecs = OFFLINE_SOLVER_TIME_LIMIT;
							doRobustLRTDP(currentAbstractState, bellmanError, 40);
						} else if (PLANEJAMENTO == ONLINE) {
							_nTimeLimitSecs = ONLINE_SOLVER_TIME_LIMIT;
							doRobustLRTDP(currentAbstractState, bellmanError, 40);
						}
					} catch (TimeLimitExceededException e1) {
						e1.printStackTrace();
					}
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

			
			stateAssign.remove(0);
			Double valorBloco = _context.evaluate(stochasticBisimulation, stateAssign);
			stateAssign.add(0, null);
			ArrayList <Boolean> representant = mdp.getRepresentant(valorBloco);
			if (representant != null) {
				ActionIntervalTransition at = pi.get(representant);
				// System.out.println("Assignments: " + e.getAtribuicoes());
				if (at != null) {
					action_taken = at.getAction()._csActionName._string;
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
	
	public boolean hasNegativeLeaves (Integer decisionDiagram) {
		HashSet <ADDDNode> leaves = new HashSet <ADDDNode>();
		_context.collectLeaves(decisionDiagram, leaves);
		Iterator <ADDDNode> iterator = leaves.iterator();
		while (iterator.hasNext()) {
			ADDDNode leaf = iterator.next();
			if (leaf._dLower < 0.0d) {
				return true;
			}
		}
		return false;
	}
	
	private HashMap <Pair<CString, Integer>, Integer> fillProbabilityDistributions(
			Integer stochasticBisimulation, HashMap <Double, ArrayList<ArrayList <Boolean>>> mapBlockIDsToDNF) {
		// _context.getGraph(stochasticBisimulation).launchViewer();
		HashMap <Pair<CString, Integer>, Integer> _hmProbToReachStableBlockWithAction = new HashMap <Pair<CString, Integer>, Integer>(); 
		
		for (Double blockInP : mapBlockIDsToDNF.keySet()) {
			System.out.println("Block id: " + blockInP);
			Integer stochasticBisimulationBlock = _context.getConstantNode(0.0d);
			for (ArrayList <Boolean> expr : mapBlockIDsToDNF.get(blockInP)) {
				ArrayList <Boolean> exprClone = (ArrayList<Boolean>) expr.clone();
				exprClone.remove(0);
				stochasticBisimulationBlock = DDUtils.UpdateValue(_context, stochasticBisimulationBlock, exprClone, 1.0d);
			}
			
			// _context.getGraph(stochasticBisimulationBlock).launchViewer();

			for (Pair p : _hmProbToReachBlockWithAction.keySet()) {
				CString actionName = (CString) p._o1;
				Integer bddForBlockJ = (Integer) p._o2;
				System.out.println("Action: " + actionName + ", ActionBlock: " + bddForBlockJ);
				// _context.getGraph(bddForBlockJ).launchViewer();
				Integer intersection = _context.applyInt(stochasticBisimulationBlock, bddForBlockJ, ADD.ARITH_PROD);
				if (intersection != _context.getConstantNode(0.0d)) {
					Integer probabilityToReachBlockJ = _hmProbToReachBlockWithAction.get(p);
					Integer currentProbability = null;
					if ((currentProbability = _hmProbToReachStableBlockWithAction.get(new Pair(actionName, stochasticBisimulationBlock))) == null) {
						_hmProbToReachStableBlockWithAction.put(new Pair(actionName, stochasticBisimulationBlock), probabilityToReachBlockJ);
						// _context.getGraph(probabilityToReachBlockJ).launchViewer();
					} else {
						currentProbability = _context.applyInt(currentProbability, probabilityToReachBlockJ, ADD.ARITH_SUM);
						// _context.getGraph(currentProbability).launchViewer();
						_hmProbToReachStableBlockWithAction.put(new Pair(actionName, stochasticBisimulationBlock), currentProbability);
					}
				}
			}
		}
		return _hmProbToReachStableBlockWithAction;
	}

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
		flushCaches();
		
		return reachableStates;
	}
	
	private static final String LOG_FILE = "ReachabilityModelReductionConvergence";
	private static final boolean ONLY_ESSENTIAL_VARS = true;
	private static final String OS = null;
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

	double valueFunctionS0;
	private void doRobustLRTDP(ArrayList <Boolean> currentAbstractState, double bellmanError, int horizon) throws TimeLimitExceededException {
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
					// System.out.println("V(s0) = " + valueFunction.get(initialState));
					robustLRTDP(initialState, bellmanError, horizon);
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
	
	private void robustLRTDP(ArrayList <Boolean> currentAbstractState, double bellmanError, int horizon) throws TimeOutException {
		
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
			flushCaches();
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
	
	public static class ActionIntervalTransition {
		private Action a;
		private ArrayList <IntervalProbState> actionTransitions;
		private double reward;
		private double qValue;
		
		public ActionIntervalTransition (Action a, ArrayList <IntervalProbState> actionTransitions) {
			this.a = a;
			this.actionTransitions = actionTransitions;
		}
		
		public Action getAction() {
			return a;
		}
		
		public ArrayList <IntervalProbState> getTransitions() {
			return actionTransitions;
		}
		
		public void setTransitions (ArrayList <IntervalProbState> transitions) {
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
		
		public String toString() {
			return a._csActionName._string;
		}
		
	}
	
	HashMap <ArrayList <Boolean>, ArrayList<ActionIntervalTransition>> enabledActions = new HashMap <ArrayList <Boolean>, ArrayList<ActionIntervalTransition>>(); 
	
	public boolean acaoDisponivel (ArrayList <Boolean> currentState, Action a) {
		boolean aplicavel = false;
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get (currentState);
		ArrayList <ActionIntervalTransition> acoesDisponiveis = enabledActions.get(currentState);
		
		if (acoesDisponiveis != null) {
			for (int i = 0; i < acoesDisponiveis.size(); i++) {
				ActionIntervalTransition at = acoesDisponiveis.get(i);
				if (at.getAction()._csActionName.equals(a._csActionName)) {
					aplicavel = true;
					return aplicavel;
				}
			}
		}
		return aplicavel;
	}
	
    public ActionIntervalTransition getAcao(ArrayList <Boolean> currentState, Action a) {
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get (currentState);
		ArrayList <ActionIntervalTransition> acoesDisponiveis = enabledActions.get(currentState);
		
		if (acoesDisponiveis != null) {
			for (int i = 0; i < acoesDisponiveis.size(); i++) {
				ActionIntervalTransition at = acoesDisponiveis.get(i);
				if (at.getAction()._csActionName.equals(a._csActionName)) {
					return at;
				}
			}
		}
		return null;
    }
	
    public ActionIntervalTransition getGreedyAction (ArrayList <Boolean> state) {
    	double gamma = _dDiscount;
    	
		ActionIntervalTransition acaoOtima = null;
		double qOtimo = -Double.MAX_VALUE;
		Double q = -Double.MAX_VALUE;
		boolean oneBlockAbstraction = false;
		// find best action
		for (CString a : _hmActionName2Action.keySet()) {
			Action action = _hmActionName2Action.get(a);
			ActionIntervalTransition acao;
			if (!acaoDisponivel(state, action)) {
				acao = new ActionIntervalTransition(action, new ArrayList <IntervalProbState>());
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));
	
				
				ArrayList <ArrayList<Boolean>> completeStates = getCompleteStates(atribb);
				if (completeStates.size() == 1) {
					boolean onlyNulls = true;
					ArrayList <Boolean> representant = (ArrayList<Boolean>) completeStates.get(0).clone();
					for (int k = 0; k < representant.size(); k++) {
						if (representant.get(k) != null) {
							onlyNulls = false;
							break;
						}
					}
						
					if (onlyNulls) {
						completeStates.remove(0);
						completeStates.add(atribb);
						oneBlockAbstraction = true;
					}
				}
				double recompensa = Double.MAX_VALUE;
				
				if (!oneBlockAbstraction) {
					for (ArrayList <Boolean> stateInBlock : completeStates) {
						recompensa = Math.min(recompensa, _context.evaluate(action._reward, stateInBlock));
					}
				} else {
					for (ArrayList <Boolean> stateInBlock : completeStates) {
						recompensa = Math.min(recompensa, _context.getMin(action._reward));
					}
				}
				// double recompensa = _context.evaluate(action._reward, atribb);
				// _context.getGraph(action._reward).launchViewer();
	
				acao.setReward(recompensa);
				
				// HashMap<ArrayList<Boolean>, Double> allPaths = getAllPaths(stochasticBisimulation, true);
				// Double valorBloco = _context.evaluate(stochasticBisimulation, atribb);
				
				ArrayList <IntervalProbState> transicoes = new ArrayList <IntervalProbState>();
				transicoes = computeBMDPSuccessors(atribb, completeStates, action, true, new LinkedHashSet(_context.getGIDs(stochasticBisimulation)));
				
				acao.getTransitions().addAll(transicoes);
				ArrayList <ActionIntervalTransition> acoesDisponiveis = enabledActions.get(state);
				if (acoesDisponiveis == null) {
					acoesDisponiveis = new ArrayList <ActionIntervalTransition>();
				}
				acoesDisponiveis.add(acao);
				enabledActions.put(state, acoesDisponiveis);
			} else {
			 	acao = getAcao(state, action);
			}
			
			ArrayList <IntervalProbState> transicoes = acao.getTransitions();
			
			ArrayList <ProbState> worstModel = getWorstModel(transicoes);
			
			/*
			ArrayList <ProbState> worstModel;
			if (EPSILON_MODEL_REDUCTION > 0.0d) {
				worstModel = getWorstModel(transicoes);
			} else {
				worstModel = new ArrayList <ProbState>();
				for (int i = 0; i < transicoes.size(); i++) {
					worstModel.add(new ProbState(transicoes.get(i)._dLowerProb, transicoes.get(i).nextRepresentant));
				}
			}
			*/
			
			double somatorio = 0.0d;
			
			for (int j = 0; j < worstModel.size(); j++) {
				ProbState transicao = worstModel.get(j);
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
    
	private ArrayList<ProbState> getWorstModel(
			ArrayList<IntervalProbState> transitions) {
		
		/*
		List<Map.Entry<ArrayList <Boolean>, Double>> entries =
			  new ArrayList<Map.Entry<ArrayList <Boolean>, Double>>(valueFunction.entrySet());
			Collections.sort(entries, new Comparator<Map.Entry<ArrayList <Boolean>, Double>>() {
			  public int compare(Map.Entry<ArrayList <Boolean>, Double> a, Map.Entry<ArrayList <Boolean>, Double> b){
				  return a.getValue().compareTo(b.getValue()); // ordem crescente
			  }
		});
		*/
		
		/*
		for (int i = 0; i < transitions.size(); i++) {
			IntervalProbState intervaledOutcome = transitions.get(i);
			ArrayList <Boolean> nextRepresentantClone = (ArrayList<Boolean>) transitions.get(i).nextRepresentant.clone();
			intervaledOutcome.nextRepresentantValue = valueFunction.get(nextRepresentantClone);
		}
		*/
		
		Collections.sort(transitions);
		
		ArrayList<ProbState> probabilityDistribution = new ArrayList <ProbState>();
		int i;
		double minBound = 0.0d;
		for (i = 0; i < transitions.size(); i++) {
			minBound += transitions.get(i)._dLowerProb;
		}
		
		i = 0;
		double bound = minBound;
		double sum = bound - transitions.get(i)._dLowerProb + transitions.get(i)._dUpperProb;
		while (sum < 0.999999d) {
			bound += -transitions.get(i)._dLowerProb + transitions.get(i)._dUpperProb;
			ProbState ps = new ProbState(transitions.get(i)._dUpperProb, transitions.get(i).nextRepresentant);
			probabilityDistribution.add(i, ps);
			i++;
			sum = bound - transitions.get(i)._dLowerProb + transitions.get(i)._dUpperProb;
		}
		
		int r = i;
		
		ProbState pr = new ProbState (1 - (bound - transitions.get(r)._dLowerProb), transitions.get(r).nextRepresentant);
		probabilityDistribution.add(r, pr);
		for (i = r + 1; i < transitions.size(); i++) {
			ProbState ps = new ProbState(transitions.get(i)._dLowerProb, transitions.get(i).nextRepresentant);
			probabilityDistribution.add(i, ps);
		}
		
		return probabilityDistribution;
	}

	public ArrayList <Boolean> updateState(ArrayList <Boolean> state) {
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionIntervalTransition acaoOtima = getGreedyAction (state);
		pi.put(stateClone, acaoOtima);
		valueFunction.put(stateClone, acaoOtima.getQValue());
		return state;
	}
	
	public ArrayList <Boolean> obtemProximoEstado (ArrayList <Boolean> estado, MDP mdp, int horizon) {
        Random rand = new Random((new Date()).getTime());
        ActionIntervalTransition acao = null;
        ArrayList <Boolean> e = null;
        double probabilidadeSorteada = 0.0d;
        int i = 0;
        
        if (PLANEJADOR == LRTDP) {
        	acao = pi.get(estado);
        }
        
        if (acao != null) {
        	ProbState t = null;
        	
        	if (USING_BINARY_SEARCH_SORTITION) {
        		ArrayList <IntervalProbState> transicoes = acao.getTransitions();
        		ArrayList <ProbState> transicoesWorstModel = getWorstModel(transicoes);
        		int indiceInicio = 0;
        		int indiceFim = transicoes.size() - 1;
        		int indiceMeio;
        		do {
        			probabilidadeSorteada = rand.nextDouble();
        		} while (probabilidadeSorteada == 0.0d);
        		while (indiceInicio <= indiceFim) {
        			indiceMeio = (indiceInicio + indiceFim) / 2;
        			if (indiceMeio >= 1) {
	        			if (transicoesWorstModel.get(indiceMeio)._dProb >= probabilidadeSorteada //  + erroAceitavel
	        					&& 
	        					(probabilidadeSorteada > transicoesWorstModel.get(indiceMeio - 1)._dProb)) {
	        				t = transicoesWorstModel.get(indiceMeio);
	        				break;
	        			} else if (transicoesWorstModel.get(indiceMeio)._dProb < probabilidadeSorteada) {
	        				indiceInicio = indiceMeio + 1;
	        			} else {
	        				indiceFim = indiceMeio - 1;
	        			}
        			} else {
        				t = transicoesWorstModel.get(indiceMeio);
        				break;
        			}
        		}
        	} else {
        		double inicioIntervalo = 0.0f;
	            double fimIntervalo = 0.0f;
	            ArrayList <IntervalProbState> transicoes = acao.getTransitions();
	            ArrayList <ProbState> transicoesWorstModel = getWorstModel(transicoes);
	            
	            do {
        			probabilidadeSorteada = rand.nextDouble();
        		} while (probabilidadeSorteada == 0.0d);
	            
	            for (i = 0; i < transicoesWorstModel.size(); i++) {
	                t = transicoesWorstModel.get(i);
	                inicioIntervalo = fimIntervalo;
	                fimIntervalo = fimIntervalo + t._dProb;
	                if ((probabilidadeSorteada > inicioIntervalo) && (probabilidadeSorteada < fimIntervalo + 0.00000001f)) {
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
	
	ArrayList <CString> essentialVars = null;
	LinkedHashSet <Integer> essentialFluents = null;
	
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
		if (essentialVars == null) {
			essentialVars = new ArrayList <CString>();
			Iterator <Integer> iterator = essentialFluents.iterator();
			while (iterator.hasNext()) {
				Integer varID = iterator.next();
				CString varName = new CString((String) _context._hmID2VarName.get(varID));
				essentialVars.add(varName);
			}
		}
		
		// for (CString x : _alStateVars) {
		for (CString x : essentialVars) {
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
	/**
	 * M�todo verifica se o estado atual j� convergiu. Para isso, olha os
	 * estados seguinte e verifica se todos j� convergiram. Utilizado na
	 * implementa��o do (LRTDP). Obs: J� foi adaptado para funcionar com R(s,a).
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

			ActionIntervalTransition at = getGreedyAction(estado);
			double residual = Math.abs(valueFunction.get(estado) - at.getQValue());
			if (residual > bellmanError) {
				rv = false;
				continue;
			}
			
			// estado = updateState(estado);
			
			ArrayList<IntervalProbState> transicoes = at.getTransitions();
			ArrayList<ArrayList <Boolean>> uniao = new ArrayList<ArrayList <Boolean>>();
			uniao.addAll(closed);
			uniao.addAll(open);
			ArrayList <ProbState> transicoesWorstModel = getWorstModel(transicoes);
			/*
			ArrayList <ProbState> transicoesWorstModel;
			if (EPSILON_MODEL_REDUCTION > 0.0d) {
				transicoesWorstModel = getWorstModel(transicoes);
			} else {
				transicoesWorstModel = new ArrayList <ProbState>();
				for (int i = 0; i < transicoes.size(); i++) {
					transicoesWorstModel.add(new ProbState(transicoes.get(i)._dLowerProb, transicoes.get(i).nextRepresentant));
				}
			}
			*/
			
			for (int j = 0; j < transicoesWorstModel.size(); j++) {
				ProbState t = transicoesWorstModel.get(j);
				double probabilidade = t._dProb;
				
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
		
		if (OS.indexOf("nix") >= 0 || OS.indexOf("nux") >= 0 || OS.indexOf("aix") >= 0) {
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
				System.out.println ("Current action: " + a);
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

				System.out.println("Heuristica admiss�vel: "
						+ heuristicaAdmissivel);
				// System.exit(0);
			} catch (Exception e) {
				System.err.println("Exception at " + _nIter + " iterations.");
				e.printStackTrace(System.err);
				System.exit(1);
			} catch (Throwable t) {
				System.out.println("Throwable lan�ado. Subclasse de java.lang.Error: " + t.getMessage());
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
					mdp.setErroMaximoPermitido((float) bellmanError);
					if (pi == null) {
						pi = new HashMap <ArrayList <Boolean>, ActionIntervalTransition>();
					}
					System.out.println(">>> MDP instantiated.");
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
		if (EPSILON_MODEL_REDUCTION >= 0.0d) {
			timeInfoContent.append("EPSILON=" + EPSILON_MODEL_REDUCTION + "\n");
		}
		timeInfoContent.append("HOMOGENEOUS_PARTITION_SIZE=" + partitionSize + "\n");
		if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
			timeInfoContent.append("REACHABILITY_TIME=" + ((double) reachabilityTime.getTotalMilisegundos() / 1000.0d) + "\n");
		}
		
		if (ONLY_BISIMULATION) {
			timeInfoContent.append("BISIMULATION_TIME=" + ((double) bisimulationTime.getTotalMilisegundos() / 1000.0d) + "\n");
			if (MODEL_MINIMIZATION) {
				geradorDeArquivo.geraArquivo("ReachMMFS_OnlyBisimulation" + SEPARATOR + _sInstanceName + "_Time.txt");
			} else {
				geradorDeArquivo.geraArquivo("ReachMRFS_OnlyBisimulation" + SEPARATOR + _sInstanceName + "_Time.txt");
			}
		} else {
			timeInfoContent.append("BISIMULATION_TIME=" + ((double) bisimulationTime.getTotalMilisegundos() / 1000.0d) + "\n");
			timeInfoContent.append("PLANNER_TIME=" + ((double) lrtdpTime.getTotalMilisegundos() / 1000.0d) + "\n");
			timeInfoContent.append("REWARD=" + reward + "\n");
			timeInfoContent.append("V*(s0)=" + valueFunctionS0 + "\n");
			
				
			if (ONLY_USEFUL_PARTITIONS) {
				if (EPSILON_MODEL_REDUCTION == 0.0d) {
					if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
						if (ONLY_BISIMULATION) {
							geradorDeArquivo.geraArquivo("ReachabilityBisimulationImpl2Time" + SEPARATOR + _sInstanceName + "_Time.txt");
						} else {
							geradorDeArquivo.geraArquivo("ReachabilityMMPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
						}
					} else {
						if (ONLY_BISIMULATION) {
							geradorDeArquivo.geraArquivo("BisimulationTime" + SEPARATOR + _sInstanceName + "_Time.txt");
						} else {
							geradorDeArquivo.geraArquivo("BisimulationPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
						}
					}
				}
			} else {
				if (MODEL_MINIMIZATION == false && EPSILON_MODEL_REDUCTION == 0.0d) {
					geradorDeArquivo.geraArquivo("OriginalBisimulationTime" + SEPARATOR + _sInstanceName + "_Time.txt");
				} else {
					if (MODEL_MINIMIZATION == true && EPSILON_MODEL_REDUCTION > 0.0d) {
						String directory = "Reachability" + EPSILON_MODEL_REDUCTION + "MRPlannerTime";
						geradorDeArquivo.geraArquivo(directory + SEPARATOR + _sInstanceName + "_Time.txt");
					} else if (MODEL_MINIMIZATION == true && EPSILON_MODEL_REDUCTION == 0.0d) {
						geradorDeArquivo.geraArquivo("ReachabilityMMPlannerTime" + SEPARATOR + _sInstanceName + "_Time.txt");
					}
				}
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
		bisimulationInfoContent.append("Epsilon for aggregation: " + EPSILON_MODEL_REDUCTION + "\n");
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
	 * Devolve a altura de um ADD baseado no conceito de altura para �rvores bin�rias.
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
					// System.out.println("_dLower e _dUpper s�o praticamente iguais.");
					// System.out.println("Assign: " + assign);
					// System.out.println("_dLower = _dUpper = " +
					// leaf._dLower)
					if (leaf._dLower != 0.0d) {
						Double recompensa = leaf._dLower;
						estadoRecompensa.put((ArrayList<Boolean>) assign.clone(),
							recompensa);
					}
				} else {
					// Calcula a m�dia.
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
	
	private void freeAllPrimes (LinkedHashMap <Integer, Boolean> primesUsed) {
		for (Integer prime : primesUsed.keySet()) {
			if (primesUsed.get(prime).equals(true)) {
				primesUsed.put(prime, false);
			} else {
				// Como o mapa está ordenado, depois de encontrar um primo que não foi utilizado,
				// todos os primos seguintes da lista também não foram utilizados.
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
	
	private Integer getNextFreePrime (LinkedHashMap <Integer, Boolean> localPrimeNumbers) {
		Integer freePrime = null;
		for (Integer prime : localPrimeNumbers.keySet()) {
			if (localPrimeNumbers.get(prime).equals(false)) {
				localPrimeNumbers.put(prime, true);
				freePrime = prime;
				break;
			}
		}
		
		if (freePrime == null) {
			missingPrimes++;
			System.out.println("Impossible to go on, its necessary to generate more prime numbers.");
			ArrayList <Integer> primeNumbers = soe.getPrimeNumbers(soe.recomputeMappingOfNumbers());
			System.out.println("More prime numbers were found.");
			for (Integer prime : primeNumbers) {
				if (!localPrimeNumbers.keySet().contains(prime)) {
					localPrimeNumbers.put(prime, false);
				}
			}
			freePrime = getNextFreePrime (localPrimeNumbers);
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
    			// modificar este trecho para inserir n�mero primo.
    			// necess�rio de um contador global de n�meros primos de forma
    			// que sempre que necess�rio, a contagem seja incrementada e seja
    			// garantido que um n�mero primo diferente ser� obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necess�rio alguma regra para n�o separar blocos...
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
	
	public int reduceRemapLeaves(int id, HashMap <Double, Integer> oldValueToPrime, LinkedHashMap<Integer, Boolean> localPrimesUsed, boolean remapZeros) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
    	if (Fr == null) {
    		ADDNode nodeKey = _context.getNode(id);
    		if (nodeKey instanceof ADDINode) {
	    		Integer Fh = reduceRemapLeaves(((ADDINode)nodeKey)._nHigh, oldValueToPrime, localPrimesUsed, remapZeros);
	    		Integer Fl = reduceRemapLeaves(((ADDINode)nodeKey)._nLow, oldValueToPrime, localPrimesUsed, remapZeros);
	    		Integer Fvar = ((ADDINode)nodeKey)._nTestVarID;
	    		Fr  =_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	} else {
    			ADDDNode nod = (ADDDNode)nodeKey;
    			// modificar este trecho para inserir numero primo.
    			// necessario de um contador de numeros primos de forma
    			// que sempre que necessario, a contagem seja incrementada e seja
    			// garantido que um numero primo diferente sera obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necessario alguma regra para nao separar blocos...
    			if (oldValueToPrime.get(nod._dUpper) == null) { // essa folha ainda nao foi visitada
    				if (remapZeros) {
    					int newValue = getNextFreePrime(localPrimesUsed);
    					oldValueToPrime.put(nod._dUpper, newValue);
    					return _context.getConstantNode(newValue);
    				} else {
    					if (nod._dUpper == 0.0d) {
    						return _context.getConstantNode(0.0d);
    					} else {
    						int newValue = getNextFreePrime(localPrimesUsed);
        					oldValueToPrime.put(nod._dUpper, newValue);
        					return _context.getConstantNode(newValue);
    					}
    				}
    			} else { // folha ja visitada, utiliza valor existente para nao separar quando se considera outros caminhos.
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
			soe = new SieveOfEratosthenes((int) (problemDescription.getNumVars() + problemDescription.getNumActions() * problemDescription.getNumVars()) * 100); // valor base v�lido para a maior parte dos problemas abstra�dos.
		} else {
			// soe = new SieveOfEratosthenes((int) (problemDescription.getNumVars() + problemDescription.getNumActions() * problemDescription.getNumVars()) * 500); // valor base v�lido para a maior parte dos problemas abstra�dos.
			soe = new SieveOfEratosthenes(20000000); // testado e funcionando at� 40.000.000
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
			System.out.println("Normalizing and approximating the reward function...");
			_context.setPrunePrecision (EPSILON_MODEL_REDUCTION);
		 	int REPLACE_RANGE = 6;
		 	_context.setPruneType (REPLACE_RANGE);
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
				if (EPSILON_FOR_REWARD_PARTITIONS && (EPSILON_MODEL_REDUCTION > 0.0d)) {
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
				if (EPSILON_FOR_REWARD_PARTITIONS && (EPSILON_MODEL_REDUCTION > 0.0d)) {
					if (finalRewardPartition == null) {
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = newActionRewardMap.get(action);
						Integer newPartition = getPartitionFromFunction(partition, primeUsed, true);
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = newPartition;
					} else {
						Integer partition = newActionRewardMap.get(action);
						Integer newPartition = getPartitionFromFunction(partition, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context.applyInt(finalRewardPartition, newPartition, ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction(finalRewardPartition, primeUsed, false);
					}
				} else {
					// System.out.println("P^a_R = " + action._csActionName);
					if (finalRewardPartition == null) {
						Integer partition = getPartitionFromFunction(action._reward, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = partition;
					} else {
						Integer partition = getPartitionFromFunction(action._reward, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition, reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context.applyInt(finalRewardPartition, partition, ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction(finalRewardPartition, primeUsed, false);
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
		HashMap <Double, Integer> oldValueToPrime = new HashMap <Double, Integer>();
		freeAllPrimes(primeUsed);
		finalRewardPartition = getPartitionFromFunction(finalRewardPartition, primeUsed, false);
		System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < countPrimesUsed(primeUsed)) {
			maxPrimesUsed = countPrimesUsed(primeUsed);
		}
		// _context.getGraph(finalRewardPartition).launchViewer();

		// Refine the partition based on the probability of transitions for
		// each action.
		Integer newPartition = finalRewardPartition;
		Integer oldPartition;
		
		essentialFluents = new LinkedHashSet <Integer> ();
		if (ONLY_ESSENTIAL_VARS ) {
			essentialFluents.addAll(getEssentialFluents(finalRewardPartition));
		} else { // ALL VARS
			for (int i = 1; i <= _context._hmID2VarName.size() / 2; i++) {
				essentialFluents.add(i);
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
					oldValueToPrime = new HashMap <Double, Integer>();
					System.out.println("\t- " + a);
					Action action = _hmActionName2Action.get(a);
					Integer partitionOfA = partitionsOfActions.get(action);
					
					if (partitionOfA == null) {
						System.out.println("Computing the partition of " + a);
						partitionOfCurrentAction = partitionDetermining(action, usefulPartitions);
						partitionOfCurrentAction = getPartitionFromFunction(partitionOfCurrentAction, primeUsed, false);
						// _context.getGraph(partitionOfCurrentAction).launchViewer();
						if (MODEL_MINIMIZATION) {
							// _context.getGraph(partitionOfCurrentAction).launchViewer();
							HashSet leavesBefore = new HashSet();
							HashSet leavesAfter = new HashSet();
							_context.collectLeaves(partitionOfCurrentAction, leavesBefore);
							long numberOfLeavesBefore = leavesBefore.size();
							System.out.println("Leaves before: " + numberOfLeavesBefore);
							partitionOfCurrentAction = blockMerge (partitionOfCurrentAction, action);
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
					newPartition = getPartitionFromFunction (newPartition, primeUsed, false);
					// _context.getGraph(newPartition).launchViewer();
				}
			}
			
			oldValueToPrime = new HashMap <Double, Integer> ();
			freeAllPrimes(primeUsed);
			newPartition = getPartitionFromFunction(newPartition, primeUsed, false);
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
	
	HashMap <Pair<Double, Action>, Integer> _hmprobabilityDistributionForActions = new HashMap <Pair<Double, Action>, Integer>();
	HashMap <Pair<CString, Integer>, Integer> _hmProbToReachBlockWithAction = new HashMap <Pair<CString, Integer>, Integer>();
	
	private Integer blockMerge (Integer partitionOfCurrentAction, Action action) {
		// System.out.println("Partition received");
		// _context.getGraph(partitionOfCurrentAction).launchViewer();
		LinkedHashMap <Integer, Boolean> localPrimes = (LinkedHashMap<Integer, Boolean>) primeUsed.clone();
		freeAllPrimes(localPrimes);
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
		
		// Para cada bloco e para acao atual, obtem a funcao de transicao.
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
		
		// Para cada bloco que pode ser alcan�ado, gere uma parti��o distinta e insira a mesma na intersec��o.
		Integer partitionIntersection = _context.getConstantNode(1.0d);
		int jCounter = 1;
		for (Double blockJ : blocks) {
			ArrayList <ArrayList <Boolean>> dnfForBlockJ = mapBlockIDsToDNF.get(blockJ);
			Integer blockJBDD = _context.getConstantNode(0.0d);
			for (ArrayList <Boolean> expr : dnfForBlockJ) {
				ArrayList <Boolean> exprClone = (ArrayList<Boolean>) expr.clone();
				exprClone.remove(0);
				blockJBDD = DDUtils.UpdateValue(_context, blockJBDD, exprClone, 1.0d);
			}
			// _context.getGraph(blockJBDD).launchViewer();
			
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
			_hmProbToReachBlockWithAction.put(new Pair (action._csActionName, blockJBDD), stableBlocksWRTBlockJ);
			
			// Agrupa estados que tem a probabilidade dentro de um epsilon de alcan�ar um bloco de estados.
			if (EPSILON_MODEL_REDUCTION > 0.0d) {
			 	_context.setPrunePrecision (EPSILON_MODEL_REDUCTION);
			 	int REPLACE_RANGE = 6;
			 	_context.setPruneType (REPLACE_RANGE);
				stableBlocksWRTBlockJ = _context.pruneNodes (stableBlocksWRTBlockJ);
			}
			
			Integer partitionStableWRTBlockJ = getPartitionFromFunction(stableBlocksWRTBlockJ, localPrimes, true);
			partitionIntersection = _context.applyInt(partitionIntersection, partitionStableWRTBlockJ, ADD.ARITH_PROD);
			validateDoublePrecision(partitionIntersection);
			freeAllPrimes(localPrimes);
			partitionIntersection = getPartitionFromFunction (partitionIntersection, localPrimes, true);
		}
		
		partitionIntersection = getPartitionFromFunction (partitionIntersection, primeUsed, true);
		
		System.out.println("Partition returned");
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
	
	public ArrayList <ArrayList <Boolean>> getCompleteStates (ArrayList <Boolean> stateClone) {
		ArrayList <Boolean> originalState = (ArrayList<Boolean>) stateClone.clone();
		ArrayList <ArrayList<Boolean>> statesInAssignment = new ArrayList <ArrayList<Boolean>>();
		ArrayList <ArrayList<Boolean>> completeStates = new ArrayList <ArrayList <Boolean>> ();
		double valorBloco = _context.evaluate(stochasticBisimulation, stateClone);
		ArrayList <ArrayList <Boolean>> dnfForBlock = mapBlockIDsToDNF.get(valorBloco);
		int size = stateClone.size() / 2;
		for (int j = 0; j < dnfForBlock.size(); j++) {
			ArrayList <Boolean> dnfClone = (ArrayList<Boolean>) dnfForBlock.get(j).clone();
			dnfClone.remove(0);
			statesInAssignment.add(dnfClone);
			while (!statesInAssignment.isEmpty()) {
				boolean complete = true;
				stateClone = statesInAssignment.remove(0);
				for (int i = 0; i < size; i++) {
					if (essentialFluents.contains(i + 1)) {
						if (stateClone.get(i) == null) {
							complete = false;
							ArrayList <Boolean> assignmentTrue = (ArrayList<Boolean>) stateClone.clone();
							ArrayList <Boolean> assignmentFalse = (ArrayList<Boolean>) stateClone.clone();
							assignmentTrue.set(i, true);
							assignmentFalse.set(i, false);
							statesInAssignment.add(assignmentTrue);
							statesInAssignment.add(assignmentFalse);
							break;
						}
					}
				}
				
				if (complete) {
					completeStates.add(stateClone);
				}
			}
		}
		return completeStates;
	}
	
	ArrayList <CString> stochasticBisimulationVarNames = null;
	private ArrayList<IntervalProbState> computeBMDPSuccessors(ArrayList <Boolean> state, ArrayList<ArrayList<Boolean>> completeStates,
			Action action, boolean extracting, LinkedHashSet <Integer> stochasticBisimulationVars) {
		
		Integer xiprime;
		HashMap <Integer, Integer> id2ADD = action._hmVarID2CPT;
		ArrayList <Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		int size = stateClone.size() / 2;
		CString _csActionName = action._csActionName;
		// for (int i = 0; i < size; i++) {
		//	if (stateClone.get(i) == null) {
		//		stateClone.set(i, false);
		//	}
		// }
		double valorBloco = _context.evaluate(stochasticBisimulation, stateClone);
		ArrayList <ArrayList <Boolean>> dnfForBlock = mapBlockIDsToDNF.get(valorBloco);
		
		
		// System.out.println("Essential fluents: " + essentialFluents);
		
		
		
		// int stateCounter = 0;
		// for (ArrayList <Boolean> completeState : completeStates) {
		//	System.out.println(stateCounter++ + " " + completeState);
		//	System.out.println("\tReward for current action: " + _context.evaluate(action._reward, completeState));
		// }
		
		
		if (stochasticBisimulationVarNames == null) {
			stochasticBisimulationVarNames = new ArrayList <CString>();
			Iterator <Integer> iterator = stochasticBisimulationVars.iterator();
			while (iterator.hasNext()) {
				Integer varID = iterator.next();
				CString varName = new CString((String) _context._hmID2VarName.get(varID));
				stochasticBisimulationVarNames.add(varName);
			}
		}
		
		HashMap <ArrayList <Boolean>, Integer> stateToDistribution = new HashMap <ArrayList <Boolean>, Integer>();
		for (ArrayList <Boolean> stateTemp : completeStates) {
			Integer multCPTs = _context.getConstantNode(1.0d);
			for (CString x : stochasticBisimulationVarNames) {
				xiprime = (Integer) _context._hmVarName2ID
						.get(_translation._hmPrimeRemap.get(x._string));
				Integer cpt_a_xiprime = id2ADD.get(xiprime);
				double probTrue, probFalse;
				int levelprime = (Integer) _context._hmGVarToLevel.get(xiprime);
				stateTemp.set(levelprime, true);
				probTrue = _context.evaluate(cpt_a_xiprime, stateTemp);
				stateTemp.set(levelprime, null);
				// stateTemp.set(levelprime, false);
				probFalse = 1 - probTrue;
				Integer Fh = _context.getConstantNode(probTrue);
				Integer Fl = _context.getConstantNode(probFalse);
				Integer newCPT = _context.getINode(xiprime, Fl, Fh, true);
				multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
			}
			// _context.getGraph(multCPTs).launchViewer();
			HashSet <ADDDNode> multCPTLeaves = new HashSet <ADDDNode>();
			_context.collectLeaves(multCPTs, multCPTLeaves);
			
			Integer transitionBetweenBlocks = _context.getConstantNode(0.0d);
			for (Double blockID : mapBlockIDsToDNF.keySet()) {
				Integer blockDescriptionBDD = mapBlockIDToBDD.get(blockID);
				Integer nextBlockDescriptionBDD = _context.remapGIDsInt(blockDescriptionBDD, _hmStringPrimeVarID2VarID);
				Integer tempMultCPT = _context.applyInt(nextBlockDescriptionBDD, multCPTs, ADD.ARITH_PROD);
				// _context.getGraph(tempMultCPT).launchViewer();
				LinkedHashSet <Integer> multCPTGIDs = new LinkedHashSet<Integer>(_context.getGIDs(tempMultCPT));
				
				// for (Integer gid : multCPTGIDs) {
				//  	tempMultCPT = _context.opOut(tempMultCPT, gid, ADD.ARITH_SUM);
				// }
				// ADDDNode result = (ADDDNode) _context.getNode(tempMultCPT);
				// Double sum = result._dLower;
				
				
				Double sum = 0.0d;
				ArrayList <Boolean> nextAssign = new ArrayList <Boolean>();
				for (int i = 0; i <= _context._alOrder.size(); i++) {
					nextAssign.add(null);
				}
				// _context.getGraph(tempMultCPT).launchViewer();
				sum = getDDSum(_context.getNode(tempMultCPT), nextAssign, sum);
				tempMultCPT = _context.applyInt(blockDescriptionBDD, _context.getConstantNode(sum), ADD.ARITH_PROD);
				
				
				// tempMultCPT = _context.applyInt(blockDescriptionBDD, tempMultCPT, ADD.ARITH_PROD);
				transitionBetweenBlocks = _context.applyInt(transitionBetweenBlocks, tempMultCPT, ADD.ARITH_SUM);
			}
			multCPTs = transitionBetweenBlocks;
			// _context.getGraph(multCPTs).launchViewer();
			stateToDistribution.put(stateTemp, multCPTs);
		}
		
		
		Integer minTransitionFunction = _context.getConstantNode(Double.MAX_VALUE);
		Integer maxTransitionFunction = _context.getConstantNode(-Double.MAX_VALUE);
		for (ArrayList <Boolean> stateTemp : stateToDistribution.keySet()) {
			Integer transitionFromStateTemp = stateToDistribution.get(stateTemp);
			// _context.getGraph(transitionFromStateTemp).launchViewer();
			minTransitionFunction = _context.applyInt(minTransitionFunction, transitionFromStateTemp, ADD.ARITH_MIN);
			maxTransitionFunction = _context.applyInt(maxTransitionFunction, transitionFromStateTemp, ADD.ARITH_MAX);
		}
		
		minTransitionFunction = _context.remapGIDsInt(minTransitionFunction, _hmStringPrimeVarID2VarID);
		maxTransitionFunction = _context.remapGIDsInt(maxTransitionFunction, _hmStringPrimeVarID2VarID);
		// _context.getGraph(minTransitionFunction).launchViewer();
		// _context.getGraph(maxTransitionFunction).launchViewer();

		// ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		ArrayList<IntervalProbState> transicoes = new ArrayList<IntervalProbState>();

		ArrayList<Boolean> nextAssignment = new ArrayList<Boolean>();
		for (int i = 0; i <= _context._alOrder.size(); i++) {
			nextAssignment.add(null);
		}
		
		boolean minExtraction = true;
		optimizedCPTInOrderSearch(_context.getNode(minTransitionFunction), nextAssignment, transicoes, true, minExtraction);
		minExtraction = false;
		optimizedCPTInOrderSearch(_context.getNode(maxTransitionFunction), nextAssignment, transicoes, true, minExtraction);
		/*
		for (int i = 0; i < transicoes.size(); i++) {
			if (transicoes.get(i)._dLowerProb > transicoes.get(i)._dUpperProb) {
				double temp = transicoes.get(i)._dLowerProb;
				transicoes.get(i)._dLowerProb = transicoes.get(i)._dUpperProb;
				transicoes.get(i)._dUpperProb = temp;
			}
		}
		*/
		
		flushCaches();
		
		return transicoes;
	}

	/**
	 * Modificar para nao utilizar mais ArrayList <ProbState>
	 * @param state
	 * @param iD2ADD
	 * @param _csActionName
	 * @return
	 */
	/*
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
		if (essentialVars == null) {
			essentialVars = new ArrayList <CString>();
			Iterator <Integer> iterator = essentialFluents.iterator();
			while (iterator.hasNext()) {
				Integer varID = iterator.next();
				CString varName = new CString((String) _context._hmID2VarName.get(varID));
				essentialVars.add(varName);
			}
		}
		
		// for (CString x : _alStateVars) {
		for (CString x : essentialVars) {
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
		
		_context.getGraph(multCPTs).launchViewer();
		
		optimizedCPTInOrderSearch(_context.getNode(multCPTs), assign, transicoes, extracting);
		
		// How this can be done with BMDPs transition?
		// if (USING_BINARY_SEARCH_SORTITION) {
		//	for (int i = 1; i < transicoes.size(); i++) {
		//		double probabilidadeI = transicoes.get(i)._dProb;
		//		double probabilidadeIAnterior = transicoes.get(i - 1)._dProb;
		//		transicoes.get(i)._dProb = probabilidadeI + probabilidadeIAnterior;
		//	}
		//}
		// transicoes.get(transicoes.size() - 1)._dProb = 1.0d;

		return transicoes;
	}
	*/
	public Double getDDSum(ADDNode node, ArrayList<Boolean> nextAssign, Double sum) {
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
				ArrayList<Boolean> assignFalse = (ArrayList<Boolean>) nextAssign
						.clone();
				assignFalse.set(level_var, new Boolean(false));
				sum = getDDSum(lowNode, assignFalse, sum);

				// Expande a subarvore high
				ArrayList<Boolean> assignTrue = (ArrayList<Boolean>) nextAssign
						.clone();
				assignTrue.set(level_var, new Boolean(true));
				sum = getDDSum(highNode, assignTrue, sum);
			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				sum += leaf._dLower;
			}
		}
		return sum;
	}
	
	
	public void optimizedCPTInOrderSearch(ADDNode node,	ArrayList<Boolean> nextAssign, ArrayList<IntervalProbState> transicoes,
			boolean extracting, boolean minExtraction) {
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
				ArrayList<Boolean> assignFalse = (ArrayList<Boolean>) nextAssign
						.clone();
				assignFalse.set(level_var, new Boolean(false));
				optimizedCPTInOrderSearch(lowNode, assignFalse, transicoes,
						extracting, minExtraction);

				// Expande a subarvore high
				ArrayList<Boolean> assignTrue = (ArrayList<Boolean>) nextAssign
						.clone();
				assignTrue.set(level_var, new Boolean(true));
				optimizedCPTInOrderSearch(highNode, assignTrue, transicoes,
						extracting, minExtraction);

			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidade = 0d;
				if (minExtraction) {
					probabilidade = leaf._dLower;
				} else {
					probabilidade = leaf._dUpper;
				}
				// Adiciona apenas os estados com probabilidade maior que de
				// serem alcançados
				if (probabilidade > 0.0d) {
					
					@SuppressWarnings("unchecked")
					ArrayList<Boolean> newAssign = (ArrayList<Boolean>) nextAssign
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
						// Transicao para um estado que ja foi adicionado ao BMDP.
						boolean transitionExists = false;
						for (int i = 0; i < transicoes.size(); i++) {
							IntervalProbState t = transicoes.get(i);
							double valorBlocoAlState = getValorBloco (t.nextRepresentant);
							ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
							if (alStateRepresentant.equals(representantAux)) {
								
								if (!minExtraction && t._dUpperProb == 0.0d) {
									t._dUpperProb = t._dUpperProb + probabilidade.floatValue();
								}
								transitionExists = true;
								break;
							}
						}
							
						if (!transitionExists) {
							if (minExtraction) {
								IntervalProbState t = new IntervalProbState(probabilidade, 0.0d, representantAux);
								transicoes.add(t);
							} else {
								IntervalProbState t = new IntervalProbState(0.0d, probabilidade, representantAux);
								transicoes.add(t);
							}
						}
						
						if (valueFunction.get(representantAux) == null) {
							valueFunction.put(representantAux, heuristicaAdmissivel);
							solved.put(representantAux, false);
						}
					} else {
						// Estado seguinte que ainda nao esta no BMDP.
						if (extracting) {
							HashSet blocos = new HashSet();
							_context.collectLeaves(stochasticBisimulation, blocos);
								
							ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) newAssign.clone();
							stateAssignClone.remove(0);
							if (!hasNulls) {
								valorBloco = _context.evaluate(stochasticBisimulation, stateAssignClone);
								stateAssignClone.add(0, null);
								ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, stateAssignClone);
								if (minExtraction) {
									IntervalProbState t = new IntervalProbState(probabilidade, 0.0d, representant);
									transicoes.add(t);
								} else {
									IntervalProbState t = new IntervalProbState(0.0d, probabilidade, representant);
									transicoes.add(t);
								}
								
								if (valueFunction.get(representant) == null) {
									valueFunction.put(representant, heuristicaAdmissivel);
									solved.put(representant, false);
								}
							} else {
								// stateAssignClone.add(0, null);
								// HashSet <ArrayList <Boolean>> validAssignments = new HashSet <ArrayList <Boolean>>();
								// findValidAssignments(nextAssign, validAssignments, (nextAssign.size() / 2) - 1);
								// for (ArrayList <Boolean> assignment : validAssignments) {
								IntervalProbState t = null;
								newAssign.remove(0);
								valorBloco = _context.evaluate(stochasticBisimulation, newAssign);
								newAssign.add(0, null);
									
								ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, newAssign);
								boolean transitionExists = false;
								for (int i = 0; i < transicoes.size(); i++) {
									t = transicoes.get(i);
									double valorBlocoAlState = getValorBloco (t.nextRepresentant);
									ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
									if (alStateRepresentant.equals(representant)) {
										if (!minExtraction && t._dUpperProb == 0.0d) {
											t._dUpperProb = t._dUpperProb + probabilidade.floatValue();
										}
										transitionExists = true;
										break;
									}
								}
										
								if (!transitionExists) {
									if (minExtraction) {
										t = new IntervalProbState(probabilidade, 0.0d, newAssign);
										transicoes.add(t);
									} else {
										t = new IntervalProbState(0.0d, probabilidade, newAssign);
										transicoes.add(t);
									}
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
	
	
	public void optimizedBMDPCPTInOrderSearch(ADDNode node,	ArrayList<Boolean> assign, ArrayList<IntervalProbState> transicoes,
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
				optimizedBMDPCPTInOrderSearch(lowNode, assignFalse, transicoes,
						extracting);

				// Expande a subarvore high
				ArrayList<Boolean> assignTrue = (ArrayList<Boolean>) assign
						.clone();
				assignTrue.set(level_var, new Boolean(true));
				optimizedBMDPCPTInOrderSearch(highNode, assignTrue, transicoes,
						extracting);

			} else if (node instanceof ADDDNode) {
				ADDDNode leaf = (ADDDNode) node;
				Double probabilidadeInferior = leaf._dLower;
				Double probabilidadeSuperior = leaf._dUpper;
				// Adiciona apenas os estados com probabilidade maior que de
				// serem alcançados
				if (probabilidadeInferior > 0.0d || probabilidadeSuperior > 0.0d) {
					
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
						// Transi��o para um estado que j� foi adicionado ao
						// MDP.
						boolean transitionExists = false;
						for (int i = 0; i < transicoes.size(); i++) {
							IntervalProbState t = transicoes.get(i);
							double valorBlocoAlState = getValorBloco (t.nextRepresentant);
							ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
							
							// if (alStateRepresentant.equals(representantAux)) {
								// t._dProb = t._dProb + probabilidadeInferior.floatValue();
								// transitionExists = true;
								// break;
							// }
						}
							
						if (!transitionExists) {
							IntervalProbState t = new IntervalProbState(probabilidadeInferior, probabilidadeSuperior, representantAux);
							transicoes.add(t);
						}
						
						if (valueFunction.get(representantAux) == null) {
							valueFunction.put(representantAux, heuristicaAdmissivel);
							solved.put(representantAux, false);
						}
					} else {
						// Estado seguinte que ainda n�o est� no MDP.
						if (extracting) {
							HashSet blocos = new HashSet();
							_context.collectLeaves(stochasticBisimulation, blocos);
								
							ArrayList<Boolean> stateAssignClone = (ArrayList<Boolean>) newAssign.clone();
							stateAssignClone.remove(0);
							if (!hasNulls) {
								valorBloco = _context.evaluate(stochasticBisimulation, stateAssignClone);
								stateAssignClone.add(0, null);
								ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, stateAssignClone);
								IntervalProbState t = new IntervalProbState(probabilidadeInferior, probabilidadeSuperior, representant);
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
									IntervalProbState t = null;
									valorBloco = _context.evaluate(stochasticBisimulation, assignment);
									assignment.add(0, null);
									
									ArrayList <Boolean> representant = mdp.setRepresentant(valorBloco, assignment);
									boolean transitionExists = false;
									for (int i = 0; i < transicoes.size(); i++) {
										t = transicoes.get(i);
										double valorBlocoAlState = getValorBloco (t.nextRepresentant);
										ArrayList <Boolean> alStateRepresentant = mdp.setRepresentant(valorBlocoAlState, t.nextRepresentant);
										// if (alStateRepresentant.equals(representant)) {
										//	t._dProb = t._dProb + probabilidadeInferior;
										//	transitionExists = true;
										//	break;
										// }
									}
										
									if (!transitionExists) {
										// t = new IntervalProbState(probabilidadeInferior, probabilidadeSuperior, representant);
										t = new IntervalProbState(probabilidadeInferior, probabilidadeSuperior, assign);
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

	private Integer partitionDetermining(Action action, ArrayList <Integer> usefulPartitions) {
		
		Integer probabilityIntersection = _context.getConstantNode(1);
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet(
				getNextStateFluents(essentialFluents));
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
				Integer head_var_gid = nextStateFluent;
				Integer cpt_dd = action._hmVarID2CPT.get(head_var_gid);
				// System.out.println("|X'| = " +  _translation._context._hmID2VarName.get(nextStateFluent));
				if (usefulPartitions.contains(cpt_dd)) {
					// _context.getGraph(cpt_dd).launchViewer();
					_context.collectLeaves(cpt_dd, leaves);
					actionLeaves.addAll(leaves);
					Integer cptDDRestrictedToTrue = _context.restrict(cpt_dd, head_var_gid, ADD.RESTRICT_HIGH);
					// _context.getGraph(cptDDRestrictedToTrue).launchViewer();
					
					Integer newCPTDDRestricted = -1;
					if (EPSILON_IN_SPLIT && (EPSILON_MODEL_REDUCTION > 0.0d)) {
						_context.setPruneType(ADD.REPLACE_RANGE);
					 	_context.setPrunePrecision (EPSILON_MODEL_REDUCTION);
						cptDDRestrictedToTrue = _context.pruneNodes (cptDDRestrictedToTrue);
					}
					
					// _context.getGraph(cptDDRestricted).launchViewer();
					Integer partitionOfFluent = getPartitionFromFunction(cptDDRestrictedToTrue, primeUsed, true);
					
					// _context.getGraph(partitionOfFluent).launchViewer();
					if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
						// _context.getGraph(reachableStates).launchViewer();
						partitionOfFluent = _context.applyInt(partitionOfFluent, reachableStates, ADD.ARITH_PROD);
						// _context.getGraph(partitionOfFluent).launchViewer();
					}
					//_context.getGraph(partitionOfFluent).launchViewer();
					probabilityIntersection = _context.applyInt(probabilityIntersection, partitionOfFluent, DD.ARITH_PROD);
					probabilityIntersection = getPartitionFromFunction(probabilityIntersection, primeUsed, false);
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
	
		
		// return partitionsWithoutRepetition; // enquanto simplifica��o n�o funciona...
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
    			// modificar este trecho para inserir n�mero primo.
    			// necess�rio de um contador global de n�meros primos de forma
    			// que sempre que necess�rio, a contagem seja incrementada e seja
    			// garantido que um n�mero primo diferente ser� obtido.
    			// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
    			
    			// necess�rio alguma regra para n�o separar blocos...
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

	private LinkedHashSet<Integer> getNextStateFluents(LinkedHashSet<Integer> fluentsOfC) {
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

	public void roundEnd(double reward) {
		timeInfo(reachabilityTime, stochasticBisimulationTime, lrtdpTime, reward);
		// System.out.println("Imprecisao 2 (Qualidade):" + ((reward - lowerBound40) / (upperBound40 - lowerBound40)));
		
		System.out
				.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out
				.println("*********************************************************");
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
		
		if (mapBlockIDToBDD != null) {
			for (Double blockID : mapBlockIDToBDD.keySet()) {
				Integer blockDescriptionBDD = mapBlockIDToBDD.get(blockID);
				if (blockDescriptionBDD != null && blockDescriptionBDD != -1) {
					_context.addSpecialNode(blockDescriptionBDD);
				}
			}
		}

		
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
