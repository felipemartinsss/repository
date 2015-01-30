package util;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.concurrent.ConcurrentLinkedQueue;

import rddl.solver.DDUtils;
import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import util.ProbState;
import rddl.translate.RDDL2Format;
import dd.discrete.ADD;
import dd.discrete.ADDBNode;
import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;
import dd.discrete.DD;

/**
 * Class that has all the method needed to compute a stochastic bisimulation. It
 * is used by the classes MRFSxxx and ReachMRFSxxx before using a planner. The
 * main method of this class is getReducedExplicitMDP.
 * 
 * @author felipemartinsss
 *
 */
public class StochasticBisimulationCommons {

	public ADD _context;

	private Integer reachableStates;

	private Integer currentLayer = -1;

	private Integer reachableStatesPrevIter;

	private HashMap<CString, Action> _hmActionName2Action; // Holds transition

	private Hashtable reduceRemapLeavesCache = new Hashtable();

	private Integer multCPTs = -1;

	private Integer succss = -1;

	private ArrayList<CString> _alStateVars;

	private RDDL2Format _translation = null;

	private HashMap _hmStringPrimeVarID2VarID = new HashMap();;

	private final static boolean ALWAYS_FLUSH = false; // Always flush DD
														// caches?

	private static Runtime RUNTIME = Runtime.getRuntime();

	public final static double FLUSH_PERCENT_MINIMUM = 0.3d; // Won't flush
																// until < this
																// amt

	private ArrayList<Integer> _alSaveNodes; // Nodes to save during cache
	// flushing

	private ArrayList<Integer> _allMDPADDs;

	private int _valueDD;

	private int _maxDD;

	private int _prevDD;

	private static boolean STOCHASTIC_BISIMULATION_COMPUTED = false;

	private Integer stochasticBisimulation = -1;

	private HashSet<Action> actionsVerified = new HashSet<Action>();

	private LinkedList<Double> allLeavesValues = new LinkedList<Double>();

	private ArrayList<CString> _alPrimeStateVars;

	private ArrayList<CString> _alActionNames;

	private int _nTimeLimitSecs;

	private long _lStartTime;

	private Cronometro stochasticBisimulationTime;

	private HashMap<Integer, Boolean> isADDRedundant;

	private ProblemDescription problemDescription;

	private static boolean BISIMULATION_WITH_REACHABILITY_ANALYSIS = true;

	private ArrayList<Integer> primeNumbers = new ArrayList<Integer>();

	private SieveOfEratosthenes soe;

	private LinkedHashMap<Integer, Boolean> primeUsed = new LinkedHashMap<Integer, Boolean>();

	private static boolean MODEL_MINIMIZATION = false;

	private static boolean ONLY_USEFUL_PARTITIONS = true; // This variable cannot be true if MODEL_MINIMIZATION is true.

	private ArrayList<Integer> usefulPartitions;

	private int usefulPartitionsOriginalSize;

	private double EPSILON_MODEL_REDUCTION = 0.0d; // use 0.05 for the
													// approx_example

	private Hashtable simplifyPartitionCache = new Hashtable();

	private Integer rewardPartitionSize = null;

	private static final boolean ONLY_ESSENTIAL_VARS = true;

	private boolean IGNORE_NOOP = false;

	private static int partitionSize = 0;

	private double EPSILON_APROXIMATION = 0.0d; // 0.000001d;

	private boolean SHOW_PARTITION_DETERMINING = false;

	private HashMap<Integer, Integer> _hmPrimeVarID2VarID;

	private HashMap<Pair<Double, CString>, HashMap<Double, Double>> hashOfProbabilityDistribution = new HashMap<Pair<Double, CString>, HashMap<Double, Double>>();
	
	public StochasticBisimulationCommons() {}
	
	
	/**
	 * Constructor that is used by MRFSxxx and ReachMRFS classes.
	 * @param _translation
	 * @param _context
	 * @param _hmActionName2Action
	 * @param _alStateVars
	 * @param useReachabilityAnalysis
	 */
	public StochasticBisimulationCommons(RDDL2Format _translation,
			ADD _context, HashMap<CString, Action> _hmActionName2Action,
			ArrayList<CString> _alStateVars, boolean useReachabilityAnalysis) {
		this._context = _context;
		this._hmActionName2Action = _hmActionName2Action;
		this._alStateVars = _alStateVars;
		this._translation = _translation;
		BISIMULATION_WITH_REACHABILITY_ANALYSIS = useReachabilityAnalysis;

		_prevDD = _maxDD = -1;
		_valueDD = _context.getConstantNode(0d); // Initialize to 0

		_hmPrimeVarID2VarID = new HashMap<Integer, Integer>();
		_hmStringPrimeVarID2VarID = new HashMap();

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
		}

		_alSaveNodes = new ArrayList<Integer>();

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
				int cpt = _context.applyInt(dd_true, dd_false, ADD.ARITH_SUM);

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
	}

	/**
	 * Method that receives a state and a horizon and returns a set of 
	 * reachable states represented as an ADD (id).
	 * @param add_state_assign_clone
	 * @param horizon
	 * @return
	 */
	public int findReachableStates(ArrayList<Boolean> add_state_assign_clone,
			int horizon) {
		reachableStates = _context.getConstantNode(0);
		reachableStates = DDUtils.UpdateValue(_context, reachableStates,
				add_state_assign_clone, 1);
		currentLayer = DDUtils.UpdateValue(_context, reachableStates,
				add_state_assign_clone, 1);
		for (;;) {
			int nextLayer = -1;
			reachableStatesPrevIter = reachableStates;
			for (Action a : _hmActionName2Action.values()) {
				// System.out.println("\taction = " + a._csActionName._string);

				if (nextLayer == -1) {
					nextLayer = getImageSet(a, currentLayer);
				} else {
					int nextLayerForCurrentAction = getImageSet(a, currentLayer);
					nextLayer = _context.applyInt(nextLayer,
							nextLayerForCurrentAction, ADD.ARITH_SUM);
					reduceRemapLeavesCache = new Hashtable();
					nextLayer = reduceRemapLeaves(nextLayer);
				}

			}

			reachableStates = _context.applyInt(reachableStates, nextLayer,
					ADD.ARITH_SUM);
			reduceRemapLeavesCache = new Hashtable();
			reachableStates = reduceRemapLeaves(reachableStates);

			if (reachableStates.equals(reachableStatesPrevIter)) {
				break;
			}

			currentLayer = nextLayer;
			flushCaches();
		}

		flushCaches();

		return reachableStates;
	}

	/**
	 * Method used to remap leaves values from an ADD whose id is given as parameter.
	 * @param id
	 * @return
	 */
	public int reduceRemapLeaves(int id) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
		if (Fr == null) {
			ADDNode nodeKey = _context.getNode(id);
			if (nodeKey instanceof ADDINode) {
				Integer Fh = reduceRemapLeaves(((ADDINode) nodeKey)._nHigh);
				Integer Fl = reduceRemapLeaves(((ADDINode) nodeKey)._nLow);
				Integer Fvar = ((ADDINode) nodeKey)._nTestVarID;
				Fr = _context.getINode(Fvar, Fl, Fh, true);
				reduceRemapLeavesCache.put(id, Fr);
			} else {
				ADDDNode nod = (ADDDNode) nodeKey;
				return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);
			}
		}
		return Fr;
	}

	/**
	 * Method that returns and ADD representing the image set of (currentReachableSet, a).
	 * @param a
	 * @param currentReachableSet
	 * @return
	 */
	public int getImageSet(Action a, int currentReachableSet) {
		multCPTs = currentReachableSet;
		Integer xiprime, xi;
		// _context.getGraph(multCPTs).launchViewer();
		// System.out.print("\t\t");
		for (CString x : _alStateVars) {
			// System.out.print(x._string + " ");
			xiprime = (Integer) _context._hmVarName2ID
					.get(_translation._hmPrimeRemap.get(x._string));
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
		multCPTs = _context.remapGIDsInt(multCPTs, _hmStringPrimeVarID2VarID);
		// _context.getGraph(multCPTs).launchViewer();
		return multCPTs;
	}
	
	/**
	 * This method aggregates the states of a factored (implicit) MDP and
	 * generate an explicit (flat) MDP that has fewer states than the original
	 * MDP.
	 */
	@SuppressWarnings("unchecked")
	public Integer getReducedExplicitMDP(int solverTimeLimit)
			throws TimeOutException {

		// System.out.println("MemDisplay at beginning: " + MemDisplay());
		_nTimeLimitSecs = solverTimeLimit;
		_lStartTime = System.currentTimeMillis();
		stochasticBisimulationTime = new Cronometro();
		stochasticBisimulationTime.setStart();
		isADDRedundant = new HashMap<Integer, Boolean>();
		problemDescription = new ProblemDescription(_context,
				_hmActionName2Action);

		// System.out.println("Looking for prime numbers... ");
		if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
			soe = new SieveOfEratosthenes(
					(int) (problemDescription.getNumVars() + problemDescription
							.getNumActions() * problemDescription.getNumVars()) * 100); // valor
																						// base
																						// v�lido
																						// para
																						// a
																						// maior
																						// parte
																						// dos
																						// problemas
																						// abstra�dos.
		} else {
			// soe = new SieveOfEratosthenes((int)
			// (problemDescription.getNumVars() +
			// problemDescription.getNumActions() *
			// problemDescription.getNumVars()) * 500); // valor base v�lido
			// para a maior parte dos problemas abstra�dos.
			soe = new SieveOfEratosthenes(20000000); // testado e funcionando
														// at� 40.000.000
		}

		// SieveOfEratosthenes soe = new SieveOfEratosthenes();
		LinkedHashMap<Integer, Boolean> mappingOfNumbers = soe
				.getMappingOfNumbers();
		primeNumbers = soe.getPrimeNumbers(mappingOfNumbers);
		// soe.printPrimeNumbers(mappingOfNumbers);
		// soe.printPrimeNumbers(mappingOfNumbers);
		// System.out.println("Prime numbers found. How many? " +
		// primeNumbers.size());
		// System.out.println("Last prime = " +
		// primeNumbers.get(primeNumbers.size() - 1));
		for (int i = 0; i < primeNumbers.size(); i++) {
			primeUsed.put(primeNumbers.get(i), false);
		}

		int maxPrimesUsed = soe.countPrimesUsed(primeUsed);
		// System.out.println("|Primes used| = " + maxPrimesUsed);

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

		HashMap<Action, Integer> newActionRewardMap = new HashMap<Action, Integer>();

		for (CString a : _hmActionName2Action.keySet()) {
			// System.out.println("- " + a);
			Action action = _hmActionName2Action.get(a);
			Integer newActionReward = null;

			if (usefulPartitions.contains(new Integer(action._reward))) {
				if (EPSILON_MODEL_REDUCTION > 0.0d) {
					// _context.getGraph(action._reward).launchViewer();
					newActionReward = _context.applyInt(action._reward,
							ddMinReward, DD.ARITH_MINUS);
					newActionReward = _context.applyInt(newActionReward,
							ddScale, DD.ARITH_PROD);
					// _context.getGraph(newActionReward).launchViewer();
					// other way to reduce the reward partition.
					_context.setPrunePrecision(EPSILON_MODEL_REDUCTION);
					newActionReward = _context.pruneNodes(newActionReward);
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
			// _context.getGraph(action._reward).launchViewer();
			// }
			HashMap<Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
			if (usefulPartitions.contains(action._reward)) {
				if (EPSILON_MODEL_REDUCTION > 0.0d) {
					if (finalRewardPartition == null) {
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = newActionRewardMap.get(action);
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap<Double, Integer>();
						// _context.getGraph(partition).launchViewer();
						Integer newPartition = reduceRemapLeaves(partition,
								oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition,
									reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = newPartition;
					} else {
						Integer partition = newActionRewardMap.get(action);
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap<Double, Integer>();
						// _context.getGraph(partition).launchViewer();
						Integer newPartition = reduceRemapLeaves(partition,
								oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							newPartition = _context.applyInt(newPartition,
									reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context.applyInt(
								finalRewardPartition, newPartition,
								ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction(
								finalRewardPartition, primeUsed, false);
					}
				} else {
					// System.out.println("P^a_R = " + action._csActionName);
					if (finalRewardPartition == null) {
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap<Double, Integer>();
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = reduceRemapLeaves(action._reward,
								oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition,
									reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = partition;
					} else {
						reduceRemapLeavesCache = new Hashtable();
						oldValueToPrime = new HashMap<Double, Integer>();
						// _context.getGraph(action._reward).launchViewer();
						Integer partition = reduceRemapLeaves(action._reward,
								oldValueToPrime, primeUsed, true);
						// _context.getGraph(partition).launchViewer();
						if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
							partition = _context.applyInt(partition,
									reachableStates, ADD.ARITH_PROD);
						}
						// _context.getGraph(partition).launchViewer();
						finalRewardPartition = _context
								.applyInt(finalRewardPartition, partition,
										ADD.ARITH_PROD);
						finalRewardPartition = getPartitionFromFunction(
								finalRewardPartition, primeUsed, false);

					}
				}

				if (ONLY_USEFUL_PARTITIONS) {
					usefulPartitions.remove(new Integer(action._reward));
				}

			}
		}
		// System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < soe.countPrimesUsed(primeUsed)) {
			maxPrimesUsed = soe.countPrimesUsed(primeUsed);
		}

		HashSet leaves = new HashSet();
		// _context.getGraph(finalRewardPartition).launchViewer();
		_context.collectLeaves(finalRewardPartition, leaves);
		rewardPartitionSize = leaves.size();
		// System.out.println("Reward Partition computed. Size ? " +
		// rewardPartitionSize);

		// System.out.println("Reward Partition ADD's Height = " +
		// ADDHeight(_context.getNode(finalRewardPartition)));
		// System.out.println("Number of Reward Partition GIDs = " +
		// _context.getGIDs(finalRewardPartition).size());
		soe.freeAllPrimes(primeUsed);
		finalRewardPartition = getPartitionFromFunction(finalRewardPartition,
				primeUsed, false);
		// System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < soe.countPrimesUsed(primeUsed)) {
			maxPrimesUsed = soe.countPrimesUsed(primeUsed);
		}
		// _context.getGraph(finalRewardPartition).launchViewer();

		// Refine the partition based on the probability of transitions for
		// each action.
		Integer newPartition = finalRewardPartition;
		Integer oldPartition;

		LinkedHashSet<Integer> instanceFluents = new LinkedHashSet<Integer>();
		if (ONLY_ESSENTIAL_VARS) {
			instanceFluents.addAll(getEssentialFluents(finalRewardPartition));
		} else { // ALL VARS
			for (int i = 1; i <= _context._hmID2VarName.size() / 2; i++) {
				instanceFluents.add(i);
			}
		}

		HashMap<Action, Integer> partitionsOfActions = new HashMap<Action, Integer>();
		Integer partitionOfCurrentAction = null;
		// System.out.println("Computing the Full Partition...");
		int iteration = 1;
		// do {
		oldPartition = newPartition;
		// System.out.println("Iteration " + iteration);
		for (CString a : _hmActionName2Action.keySet()) {
			String actionName = a._string;
			if (IGNORE_NOOP && actionName.equals("noop")) {
				continue;
			} else {
				// System.out.println("\t- " + a);
				Action action = _hmActionName2Action.get(a);
				Integer partitionOfA = partitionsOfActions.get(action);

				if (partitionOfA == null) {
					partitionOfCurrentAction = partitionDetermining(
							instanceFluents, action, usefulPartitions);
					partitionOfCurrentAction = getPartitionFromFunction(
							partitionOfCurrentAction, primeUsed, false);
					// _context.getGraph(partitionOfCurrentAction).launchViewer();
					if (MODEL_MINIMIZATION) {
						// _context.getGraph(partitionOfCurrentAction).launchViewer();
						HashSet leavesBefore = new HashSet();
						HashSet leavesAfter = new HashSet();
						_context.collectLeaves(partitionOfCurrentAction,
								leavesBefore);
						long numberOfLeavesBefore = leavesBefore.size();
						// System.out.println("Leaves before: " +
						// numberOfLeavesBefore);

						partitionOfCurrentAction = blockMerge(newPartition,
								partitionOfCurrentAction, action);
						_context.collectLeaves(partitionOfCurrentAction,
								leavesAfter);
						long numberOfLeavesAfter = leavesAfter.size();
						// System.out.println("Leaves after: " +
						// numberOfLeavesAfter);

						// System.out.println("...");
						// _context.getGraph(partitionOfCurrentAction).launchViewer();
					}

					partitionsOfActions.put(action, partitionOfCurrentAction);
				}
				// System.out.println("|Primes used| = " + countPrimesUsed
				// (primeUsed));
				if (maxPrimesUsed < soe.countPrimesUsed(primeUsed)) {
					maxPrimesUsed = soe.countPrimesUsed(primeUsed);
				}

				newPartition = _context.applyInt(newPartition,
						partitionOfCurrentAction, ADD.ARITH_PROD);
				// newPartition = getPartitionFromFunction (newPartition,
				// primeUsed, false);
				// _context.getGraph(newPartition).launchViewer();
			}
		}

		soe.freeAllPrimes(primeUsed);
		newPartition = getPartitionFromFunction(newPartition, primeUsed, false);
		// System.out.println("Homogeneous partition");
		// _context.getGraph(newPartition).launchViewer();
		iteration++;
		// } while (!oldPartition.equals(newPartition));
		// System.out.println("|Primes used| = " + countPrimesUsed (primeUsed));
		if (maxPrimesUsed < soe.countPrimesUsed(primeUsed)) {
			maxPrimesUsed = soe.countPrimesUsed(primeUsed);
		}

		leaves = new HashSet();
		// System.out.println("|S| = " + cardinalidadeConjuntoDeEstados);
		_context.collectLeaves(newPartition, leaves);
		// System.out.println ("Full Partition computed. Size ? " +
		// leaves.size());
		partitionSize = leaves.size();

		// System.out.println("Full Partition");
		// _context.getGraph(newPartition).launchViewer();

		stochasticBisimulationTime.setEnd();
		// System.out.println("Tempo Biss. Estoc. = "
		// + cBissEstoc.getIntervalo());
		// System.out.println("The maximum number of primes used is: " +
		// maxPrimesUsed);
		// System.out.println("Number of times that we needed to recompute primes: "
		// + missingPrimes);
		return newPartition;
	}

	/**
	 * This method is used to identify the partitions that are used to determine the block split for a transition.
	 * @param fluentsOfC
	 * @param action
	 * @param usefulPartitions
	 * @return
	 */
	private Integer partitionDetermining(LinkedHashSet<Integer> fluentsOfC,
			Action action, ArrayList<Integer> usefulPartitions) {

		Integer probabilityIntersection = _context.getConstantNode(1);
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet(
				getNextStateFluents(fluentsOfC));
		ArrayList<ADDDNode> actionLeaves = new ArrayList<ADDDNode>();
		HashSet<ADDDNode> leaves;

		// if (SHOW_PARTITION_DETERMINING) {
		// System.out.println("Action: " + action._csActionName);
		// }

		// System.out.println("|X_i'| = " + nextStateFluents.size());
		Iterator<Integer> nextStateFluentsIterator = nextStateFluents
				.iterator();
		int counter = 0;
		while (nextStateFluentsIterator.hasNext()) {
			Integer nextStateFluent = nextStateFluentsIterator.next();
			if (action._hmVarID2CPT.containsKey(nextStateFluent)) {
				leaves = new HashSet<ADDDNode>();
				HashMap<Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
				Integer head_var_gid = nextStateFluent;
				Integer cpt_dd = action._hmVarID2CPT.get(head_var_gid);
				// System.out.println("|X'| = " +
				// _translation._context._hmID2VarName.get(nextStateFluent));
				if (usefulPartitions.contains(cpt_dd)) {
					// _context.getGraph(cpt_dd).launchViewer();
					_context.collectLeaves(cpt_dd, leaves);
					actionLeaves.addAll(leaves);
					Integer cptDDRestrictedToTrue = _context.restrict(cpt_dd,
							head_var_gid, ADD.RESTRICT_HIGH);
					// _context.getGraph(cptDDRestrictedToTrue).launchViewer();

					Integer newCPTDDRestricted = -1;
					if (EPSILON_APROXIMATION > 0.0d) {
						_context.setPrunePrecision(EPSILON_APROXIMATION);
						Integer cpt_dd_compact = _context.pruneNodes(cpt_dd);
						cptDDRestrictedToTrue = _context
								.restrict(cpt_dd_compact, head_var_gid,
										ADD.RESTRICT_HIGH);
					}

					// _context.getGraph(cptDDRestricted).launchViewer();
					Integer partitionOfFluent = getPartitionFromFunction(
							cptDDRestrictedToTrue, primeUsed, true);

					// _context.getGraph(partitionOfFluent).launchViewer();
					if (BISIMULATION_WITH_REACHABILITY_ANALYSIS) {
						// _context.getGraph(reachableStates).launchViewer();
						partitionOfFluent = _context.applyInt(
								partitionOfFluent, reachableStates,
								ADD.ARITH_PROD);
						// _context.getGraph(partitionOfFluent).launchViewer();
					}
					// _context.getGraph(partitionOfFluent).launchViewer();
					probabilityIntersection = _context.applyInt(
							probabilityIntersection, partitionOfFluent,
							DD.ARITH_PROD);
					probabilityIntersection = getPartitionFromFunction(
							probabilityIntersection, primeUsed, false);
					// _context.getGraph(probabilityIntersection).launchViewer();
					if (ONLY_USEFUL_PARTITIONS) {
						usefulPartitions.remove(cpt_dd);
					}
				}
				counter++;
			}

			if (SHOW_PARTITION_DETERMINING) {
				System.out.println("Current partition for the iteration: "
						+ counter);
				System.out.println("Number of nodes "
						+ _context.countExactNodes(probabilityIntersection));
				HashSet<ADDDNode> partitionBlocks = new HashSet<ADDDNode>();
				_context.collectLeaves(probabilityIntersection, partitionBlocks);
				System.out
						.println("Number of leaves " + partitionBlocks.size());
				// _context.getGraph(probabilityIntersection).launchViewer();
			}

		}
		fillAllLeavesValues(action, actionLeaves);
		// System.out.println (MemDisplay());
		// _context.getGraph(probabilityIntersection).launchViewer();

		return probabilityIntersection;
	}

	/**
	 * This method is used in MMFS. For the algorithms provided, it will not be used.
	 * @param newPartition
	 * @param partitionOfCurrentAction
	 * @param action
	 * @return
	 */
	private Integer blockMerge(Integer newPartition,
			Integer partitionOfCurrentAction, Action action) {
		// System.out.println("Partition received");
		// _context.getGraph(partitionOfCurrentAction).launchViewer();

		LinkedHashMap<Integer, Boolean> localPrimeUsed = (LinkedHashMap<Integer, Boolean>) primeUsed
				.clone();
		soe.freeAllPrimes(localPrimeUsed);

		HashMap<ArrayList<Boolean>, Double> blocksAndIdentifiers = getAllPaths(
				partitionOfCurrentAction, false);
		HashMap<Double, ArrayList<ArrayList<Boolean>>> mapBlockIDsToDNF = new HashMap<Double, ArrayList<ArrayList<Boolean>>>();
		// reduceRemapLeavesCache = new Hashtable();
		for (ArrayList<Boolean> assignment : blocksAndIdentifiers.keySet()) {
			Double assignmentBlockID = blocksAndIdentifiers.get(assignment);
			ArrayList<ArrayList<Boolean>> dnfDescription = mapBlockIDsToDNF
					.get(assignmentBlockID);
			if (dnfDescription == null) {
				dnfDescription = new ArrayList<ArrayList<Boolean>>();
			}
			dnfDescription.add(assignment);
			mapBlockIDsToDNF.put(assignmentBlockID, dnfDescription);
		}

		// blocksAndIdentifiers = removeUnreachableStateAssigns
		// (blocksAndIdentifiers);

		// blocksAndIdentifiers = getAllStates (blocksAndIdentifiers);
		ConcurrentLinkedQueue<Double> blocks = new ConcurrentLinkedQueue<Double>();
		blocks.addAll(mapBlockIDsToDNF.keySet());
		ArrayList<Double> copyOfBlocks = new ArrayList<Double>(blocks);
		System.out.println("Number of blocks:  " + copyOfBlocks.size());
		// _context.getGraph(partitionOfCurrentAction).launchViewer();

		// Para cada bloco e para a��o atual, obtem a fun��o de transi��o.
		int validBlockTransitions = 0;
		for (Double block : blocks) {
			HashMap<Double, Double> probabilityDistribution = hashOfProbabilityDistribution
					.get(new Pair(block, action._csActionName));
			probabilityDistribution = getProbabilityDistribution(
					probabilityDistribution, block, partitionOfCurrentAction,
					mapBlockIDsToDNF, action);
			hashOfProbabilityDistribution.put(new Pair(block,
					action._csActionName), probabilityDistribution);
			double sum = 0.0d;
			for (Double blockJ : probabilityDistribution.keySet()) {
				sum += probabilityDistribution.get(blockJ);
			}

			if (Math.abs(sum - 1) < 0.001) {
				validBlockTransitions++;
			}
		}

		System.out
				.println("Valid Block Transitions = " + validBlockTransitions);

		// Para cada bloco que pode ser alcan�ado, gere uma parti��o distinta e
		// insira a mesma na intersec��o.
		Integer partitionIntersection = _context.getConstantNode(1.0d);
		HashMap<Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
		int jCounter = 1;
		for (Double blockJ : blocks) {
			// System.out.println("jCounter = " + jCounter++);
			Integer stableBlocksWRTBlockJ = _context.getConstantNode(0.0d);
			for (Double blockI : blocks) {
				Pair p = new Pair(blockI, action._csActionName);
				HashMap<Double, Double> probabilityDistribution = hashOfProbabilityDistribution
						.get(p);
				Double probabilityToReachBlockJ = probabilityDistribution
						.get(blockJ);
				if (probabilityToReachBlockJ != null) {
					for (ArrayList<Boolean> assignmentInDNF : mapBlockIDsToDNF
							.get(blockI)) {
						ArrayList<Boolean> assignmentInDNFClone = (ArrayList<Boolean>) assignmentInDNF
								.clone();
						assignmentInDNFClone.remove(0);
						stableBlocksWRTBlockJ = DDUtils.UpdateValue(_context,
								stableBlocksWRTBlockJ, assignmentInDNFClone,
								probabilityToReachBlockJ);
					}
				}
			}

			// _context.getGraph(stableBlocksWRTBlockJ).launchViewer();

			// Agrupa estados que tem a probabilidade dentro de um epsilon de
			// alcan�ar um bloco de estados.
			if (EPSILON_MODEL_REDUCTION > 0.0d) {
				_context.setPrunePrecision(EPSILON_MODEL_REDUCTION);
				stableBlocksWRTBlockJ = _context
						.pruneNodes(stableBlocksWRTBlockJ);
				// _context.getGraph(stableBlocksWRTBlockJ).launchViewer();
			}

			Integer partitionStableWRTBlockJ = getPartitionFromFunction(
					stableBlocksWRTBlockJ, localPrimeUsed, true);
			partitionIntersection = _context.applyInt(partitionIntersection,
					partitionStableWRTBlockJ, ADD.ARITH_PROD);
			// validateDoublePrecision(partitionIntersection);
			soe.freeAllPrimes(localPrimeUsed);
			partitionIntersection = getPartitionFromFunction(
					partitionIntersection, localPrimeUsed, true);
		}
		partitionIntersection = getPartitionFromFunction(partitionIntersection,
				primeUsed, true);

		// System.out.println("Partition returned");
		// _context.getGraph(partitionIntersection).launchViewer();
		// Interseccao
		return partitionIntersection;

	}

	/**
	 * Gets the probability distribution when action a is applied in a block I.
	 * @param probabilityDistributionFromI
	 * @param blockI
	 * @param partitionOfCurrentAction
	 * @param mapOfBlockToDNF
	 * @param action
	 * @return
	 */
	public HashMap<Double, Double> getProbabilityDistribution(
			HashMap<Double, Double> probabilityDistributionFromI,
			Double blockI, Integer partitionOfCurrentAction,
			HashMap<Double, ArrayList<ArrayList<Boolean>>> mapOfBlockToDNF,
			Action action) {
		// Double probabilityToReachFixedBlock = -1.0d;
		// if (probabilityDistributionFromI != null) {
		// probabilityToReachFixedBlock =
		// probabilityDistributionFromI.get(fixedBlock);
		// }

		ArrayList<ArrayList<Boolean>> blockDNF = mapOfBlockToDNF.get(blockI);
		ArrayList<Boolean> validAssignment = blockDNF.get(0);
		ArrayList<Boolean> validAssignmentClone = (ArrayList<Boolean>) validAssignment
				.clone();
		validAssignmentClone.remove(0);
		if (hashOfProbabilityDistribution.get(new Pair(blockI, action)) == null) {
			int succ = computeSuccesors(validAssignmentClone,
					action._hmVarID2CPT);
			// _context.getGraph(succ).launchViewer();
			succ = _context.remapGIDsInt(succ, _hmStringPrimeVarID2VarID);
			// _context.getGraph(succ).launchViewer();
			HashMap<Double, Double> probabilityDistribution = new HashMap<Double, Double>();
			HashMap<ArrayList<Boolean>, Double> probabilityDistributionWithDNF = getAllPaths(
					succ, false);
			for (ArrayList<Boolean> assignmentInDNF : probabilityDistributionWithDNF
					.keySet()) {
				Double probability = probabilityDistributionWithDNF
						.get(assignmentInDNF);
				ArrayList<Boolean> assignmentInDNFClone = (ArrayList<Boolean>) assignmentInDNF
						.clone();
				assignmentInDNFClone.remove(0);
				Double block = _context.evaluate(partitionOfCurrentAction,
						assignmentInDNFClone);
				// probabilityDistribution.put(block, probability);
				if (probabilityDistribution.get(block) == null) {
					probabilityDistribution.put(block, probability);
				} else {
					Double oldProbability = probabilityDistribution.get(block);
					probabilityDistribution.put(block, oldProbability
							+ probability);
				}
			}
			// probabilityDistribution = getAllStates(probabilityDistribution)

			Pair<Double, CString> stateAction = new Pair<Double, CString>(
					blockI, action._csActionName);
			hashOfProbabilityDistribution.put(stateAction,
					probabilityDistribution);
		}
		probabilityDistributionFromI = hashOfProbabilityDistribution
				.get(new Pair(blockI, action._csActionName));
		return probabilityDistributionFromI;
		// probabilityToReachFixedBlock =
		// probabilityDistributionFromI.get(fixedBlock);
		// return probabilityToReachFixedBlock;
	}

	/**
	 * This method is used to extract all assignments of a decision diagram and the paths
	 * that carry to the different values (except those in which the leaves are
	 * equal to zero).
	 * 
	 * @param decisionDiagramID
	 * @return
	 */
	public HashMap<ArrayList<Boolean>, Double> getAllPaths(
			int decisionDiagramID, boolean reachableStates) {
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

	/**
	 * Compute the successors of a given state.
	 * @param state
	 * @param iD2ADD
	 * @return
	 */
	private int computeSuccesors(ArrayList state,
			HashMap<Integer, Integer> iD2ADD) {
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

		return multCPTs;
	}

	/**
	 * Compute the successors of a given state.
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
		// alEstadoProb.get(0)._dProb = 1;
		// alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		return alEstadoProb;
	}

	/**
	 * This method help compute successors to find the successors by computing 
	 * the product of the cpts for assignment.
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
						estadoRecompensa
								.put((ArrayList<Boolean>) assign.clone(),
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

	/**
	 * Fill the leaves of an ADD with values based on a lower  bound of current values
	 * that are given by intervals.
	 * @param action
	 * @param actionLeaves
	 */
	public void fillAllLeavesValues(Action action,
			ArrayList<ADDDNode> actionLeaves) {
		if (!actionsVerified.contains(action)) {
			for (ADDDNode node : actionLeaves) {
				allLeavesValues.add(node._dLower);
			}
			actionsVerified.add(action);
		}
	}

	/**
	 * Gets the fluents (i.e., state variables) that describe the next state in transition.
	 * That is, the fluents that affects the transition.
	 * @param fluentsOfC
	 * @return
	 */
	public LinkedHashSet<Integer> getNextStateFluents(
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
	 * Gets the essential fluents. 
	 * The essential fluents are those that are in reward function and those that can be obtained in CPTs from fluents in reward function.
	 * @param finalRewardPartition
	 * @return
	 */
	private LinkedHashSet<Integer> getEssentialFluents(
			Integer finalRewardPartition) {
		LinkedHashSet<Integer> essentialFluents = new LinkedHashSet<Integer>();
		LinkedHashSet<Integer> lastIterationEssentialFluents = new LinkedHashSet<Integer>();

		ConcurrentLinkedQueue<Integer> essentialFluentsDynamicList = new ConcurrentLinkedQueue<Integer>();
		// get the fluents required to represent the reward partition
		essentialFluents.addAll(_context.getGIDs(finalRewardPartition));
		essentialFluentsDynamicList.addAll(essentialFluents);

		while (!essentialFluents.equals(lastIterationEssentialFluents)) {
			lastIterationEssentialFluents = new LinkedHashSet(essentialFluents);
			for (CString a : _hmActionName2Action.keySet()) {
				// System.out.println(a);
				Action action = _hmActionName2Action.get(a);
				for (Integer fluent : essentialFluentsDynamicList) {
					// System.out.println("Id = " + fluent + " " +
					// _context._hmID2VarName.get(fluent));
					String varName = (String) _context._hmID2VarName
							.get(fluent);
					varName = varName + "'";
					Integer nextStateFluent = (Integer) _context._hmVarName2ID
							.get(varName);
					Integer probabilisticTransitionForFluent = action._hmVarID2CPT
							.get(nextStateFluent);
					Integer probabilitsticTransitionRestricted = _context
							.restrict(probabilisticTransitionForFluent,
									nextStateFluent, ADD.RESTRICT_HIGH);
					LinkedHashSet<Integer> tempFluents = new LinkedHashSet<Integer>(
							_context.getGIDs(probabilitsticTransitionRestricted));
					essentialFluents.addAll(tempFluents);
					for (Integer newFluent : essentialFluents) {
						if (!essentialFluentsDynamicList.contains(newFluent)) {
							essentialFluentsDynamicList.add(newFluent);
						}
					}
					// LinkedHashSet <Integer> fluentsFromTransitionProbability
					// =
				}
			}
		}

		// if (essentialFluents.size() == _alStateVars.size()) {
		// System.out.println("All fluents are essential.");
		// }

		return essentialFluents;
	}

	/**
	 * Given a function represented as an ADD, this algorithm generates a new ADD that represents a partition of that function.
	 * @param function
	 * @param primeMapping
	 * @param remapZeros
	 * @return
	 */
	public Integer getPartitionFromFunction(Integer function,
			LinkedHashMap<Integer, Boolean> primeMapping, boolean remapZeros) {
		HashMap<Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
		reduceRemapLeavesCache = new Hashtable();
		Integer partition = reduceRemapLeaves(function, oldValueToPrime,
				primeMapping, remapZeros);
		return partition;
	}

	/**
	 * Simplify a partition by making it more compact.
	 * @param simplerPartition
	 * @param oldValueToCounting
	 * @return
	 */
	private Integer simplifyPartition(Integer simplerPartition,
			HashMap<Double, Integer> oldValueToCounting) {
		Integer Fr = (Integer) simplifyPartitionCache.get(simplerPartition);
		if (Fr == null) {
			ADDNode nodeKey = _context.getNode(simplerPartition);
			if (nodeKey instanceof ADDINode) {
				Integer Fh = simplifyPartition(((ADDINode) nodeKey)._nHigh,
						oldValueToCounting);
				Integer Fl = simplifyPartition(((ADDINode) nodeKey)._nLow,
						oldValueToCounting);
				Integer Fvar = ((ADDINode) nodeKey)._nTestVarID;
				Fr = _context.getINode(Fvar, Fl, Fh, true);
				simplifyPartitionCache.put(simplerPartition, Fr);
			} else {
				ADDDNode nod = (ADDDNode) nodeKey;
				// modificar este trecho para inserir n�mero primo.
				// necess�rio de um contador global de n�meros primos de forma
				// que sempre que necess�rio, a contagem seja incrementada e
				// seja
				// garantido que um n�mero primo diferente ser� obtido.
				// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);

				// necess�rio alguma regra para n�o separar blocos...
				if (oldValueToCounting.get(nod._dUpper) == null) {
					int newValue = oldValueToCounting.size() + 1;
					oldValueToCounting.put(nod._dUpper, newValue);
					return _context.getConstantNode(newValue);
				} else {
					return _context.getConstantNode(oldValueToCounting
							.get(nod._dUpper));
				}
			}
		}
		return Fr;
	}

	/**
	 * Receives all partitions of the original MDP and return those that are
	 * useful and ignore the redundant ones.
	 * 
	 * @param partitions
	 */
	public ArrayList<Integer> identifyAllRedundantPartitions(
			ArrayList<Integer> partitions) {
		HashMap<Integer, Integer> partitionWORepetitionToSimplerPartition = new HashMap<Integer, Integer>();
		ArrayList<Integer> partitionsWithoutRepetition = new ArrayList<Integer>(
				(new HashSet<Integer>(partitions)));

		ArrayList<Integer> simplerPartitions = (ArrayList<Integer>) partitionsWithoutRepetition
				.clone();
		for (int i = 0; i < simplerPartitions.size(); i++) {
			HashMap<Double, Integer> oldValueToCounting = new HashMap<Double, Integer>();
			simplifyPartitionCache = new Hashtable();
			// _context.getGraph (simplerPartitions.get(i)).launchViewer();
			simplerPartitions.set(
					i,
					simplifyPartition(simplerPartitions.get(i),
							oldValueToCounting));
			partitionWORepetitionToSimplerPartition.put(
					partitionsWithoutRepetition.get(i),
					simplerPartitions.get(i));
			// _context.getGraph (simplerPartitions.get(i)).launchViewer();
		}

		for (int i = 0; i < partitionsWithoutRepetition.size(); i++) {
			Integer partitionA = partitionsWithoutRepetition.get(i);
			Integer simplePartitionA = partitionWORepetitionToSimplerPartition
					.get(partitionA);

			if (isADDRedundant.get(partitionA) == null) {
				isADDRedundant.put(partitionA, false);
			} else {
				continue;
			}

			for (int j = i + 1; j < partitionsWithoutRepetition.size(); j++) {
				Integer partitionB = partitionsWithoutRepetition.get(j);
				Integer simplePartitionB = partitionWORepetitionToSimplerPartition
						.get(partitionB);

				if (isPartitionAEqualsToPartitionB(simplePartitionA,
						simplePartitionB)) {
					// _context.getGraph(simplePartitionA).launchViewer();
					// _context.getGraph(simplePartitionB).launchViewer();
					// _context.getGraph(partitionA).launchViewer();
					// _context.getGraph(partitionB).launchViewer();
					isADDRedundant.put(partitionB, true);
				}

			}
		}
		ArrayList<Integer> usefulPartitions = getUsefulAndRedundantPartitions();
		// System.out.println("All MDP ADDs: " + _allMDPADDs.size());
		// System.out.println("Useful partitions size: " +
		// usefulPartitions.size());
		// System.out.println("Useful partitions: " + usefulPartitions);
		// print the useful partitions
		// for (int i = 0; i < usefulPartitions.size(); i++) {
		// _context.getGraph(usefulPartitions.get(i)).launchViewer();
		// }
		return usefulPartitions;

		// return partitionsWithoutRepetition; // enquanto simplifica��o n�o
		// funciona...
	}

	/**
	 * Determines if partition A represented as an ADD is equal to the partition
	 * B represented as another ADD.
	 * 
	 * @param A
	 * @param B
	 * @return
	 */
	public boolean isPartitionAEqualsToPartitionB(Integer A, Integer B) {
		return A.equals(B);
	}

	/**
	 * Show useful and redundant partitions
	 */
	public ArrayList<Integer> getUsefulAndRedundantPartitions() {
		ArrayList<Integer> usefulPartitions = new ArrayList<Integer>();
		ArrayList<Integer> redundantPartitions = new ArrayList<Integer>();
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
	 * Remap leaves of an ADD by using unique prime numbers.
	 * @param id
	 * @param oldValueToPrime
	 * @param primeMapping
	 * @param remapZeros
	 * @return
	 */
	private int reduceRemapLeaves(int id,
			HashMap<Double, Integer> oldValueToPrime,
			LinkedHashMap<Integer, Boolean> primeMapping, boolean remapZeros) {
		Integer Fr = (Integer) reduceRemapLeavesCache.get(id);
		if (Fr == null) {
			ADDNode nodeKey = _context.getNode(id);
			if (nodeKey instanceof ADDINode) {
				Integer Fh = reduceRemapLeaves(((ADDINode) nodeKey)._nHigh,
						oldValueToPrime, primeMapping, remapZeros);
				Integer Fl = reduceRemapLeaves(((ADDINode) nodeKey)._nLow,
						oldValueToPrime, primeMapping, remapZeros);
				Integer Fvar = ((ADDINode) nodeKey)._nTestVarID;
				Fr = _context.getINode(Fvar, Fl, Fh, true);
				reduceRemapLeavesCache.put(id, Fr);
			} else {
				ADDDNode nod = (ADDDNode) nodeKey;
				// modificar este trecho para inserir n�mero primo.
				// necess�rio de um contador global de n�meros primos de forma
				// que sempre que necess�rio, a contagem seja incrementada e
				// seja
				// garantido que um n�mero primo diferente ser� obtido.
				// return _context.getConstantNode(nod._dUpper > 0d ? 1d : 0d);

				// necess�rio alguma regra para n�o separar blocos...
				if (oldValueToPrime.get(nod._dUpper) == null) { // essa folha
																// ainda n�o foi
																// visitada
					if (remapZeros) {
						int newValue = soe.getNextFreePrime(primeUsed);
						oldValueToPrime.put(nod._dUpper, newValue);
						return _context.getConstantNode(newValue);
					} else {
						if (nod._dUpper == 0.0d) {
							return _context.getConstantNode(0.0d);
						} else {
							int newValue = soe.getNextFreePrime(primeUsed);
							oldValueToPrime.put(nod._dUpper, newValue);
							return _context.getConstantNode(newValue);
						}
					}
				} else { // folha j� visitada, utiliza valor existente para n�o
							// separ� quando se considera outros caminhos.
					return _context.getConstantNode(oldValueToPrime
							.get(nod._dUpper));
				}
			}
		}
		return Fr;
	}
	
	/**
	 * Frees all primes used until now.
	 * @param primeUsed
	 */
	private void freeAllPrimes (LinkedHashMap <Integer, Boolean> primeUsed) {
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				primeUsed.put(prime, false);
			} else {
				break;
			}
		}
	}
	
	/**
	 * Counts the number of primes used.
	 * @param primeUsed
	 * @return
	 */
	public int countPrimesUsed (LinkedHashMap <Integer, Boolean> primeUsed) {
		int countPrimesUsed = 0;
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				countPrimesUsed++;
			}
		}
		return countPrimesUsed;
	}
	
	/**
	 * Frees the primes used by the partition passed as reference.
	 * @param partition
	 */
	public void freeThesePrimes(int partition) {
		HashSet <ADDDNode> usedLeaves = new HashSet <ADDDNode>();
		_context.collectLeaves(partition, usedLeaves);
		for (ADDDNode node : usedLeaves) {
			Integer prime = (int) node._dLower;
			if (primeUsed.get(prime).equals(true)) {
				primeUsed.put(prime, false);
			}
		}
	}
	
	private int reachableStatesSize;
	
	/**
	 * Gets the number of reachable states in a given reachability partition.
	 * @param reachableStatesDD
	 * @return
	 */
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
	
	/**
	 * Gets the fluents used to represent a block.
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

	// utilizado
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
	
	private String SEPARATOR = "/";
	
	/**
	 * Stochastic bisimulation data.
	 * @param stochasticBisimulation
	 * @param c
	 */
	public void bisimulationInfo(String _sInstanceName, Integer stochasticBisimulation, Cronometro c) {
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
		ADDExtra addExtra = new ADDExtra(_context);
		int stochasticBisimulationADDHeight = addExtra.getNodeHeight(_context.getNode(stochasticBisimulation));
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
	 * Computes the time execution info for planners.
	 * @param reachabilityTime
	 * @param bisimulationTime
	 * @param lrtdpTime
	 * @param reward
	 */
	public void plannerTimeInfo (String _sInstanceName, Cronometro reachabilityTime, Cronometro bisimulationTime, Cronometro plannerTime, double reward, double valueFunctionS0, String plannerName) {
		StringBuffer timeInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (timeInfoContent);
		double totalTime = 0.0d;
		// double reachabilityTimeVal = reachabilityTime.getTotalMilisegundos() / 1000.0d;
		double bisimulationTimeVal = (double) bisimulationTime.getTotalMilisegundos() / 1000.0d;
		double plannerTimeVal = 0.0d;
		if (plannerTime != null) {
			plannerTimeVal = (double) plannerTime.getTotalMilisegundos() / 1000.0d;
		}
		totalTime = bisimulationTimeVal + plannerTimeVal;
		timeInfoContent.append("INSTANCE=" + _sInstanceName + "\n");
		// timeInfoContent.append("REACHABILITY_TIME=" + reachabilityTimeVal + "\n");
		timeInfoContent.append("HOMOGENEOUS_PARTITION_SIZE=" + partitionSize + "\n");
		timeInfoContent.append("BISIMULATION_TIME=" + bisimulationTimeVal + "\n");
		timeInfoContent.append("PLANNER_TIME=" + plannerTimeVal + "\n");
		timeInfoContent.append("TOTAL_TIME=" + totalTime + "\n");
		timeInfoContent.append("REWARD=" + reward + "\n");
		timeInfoContent.append("V*(s0)=" + valueFunctionS0 + "\n");
		geradorDeArquivo.geraArquivo(plannerName + SEPARATOR + _sInstanceName + "_Time.txt");
	}
	
	
	/**
	 * Computes the time information computed to stochastic bisimulation and planners.
	 * @param reachabilityTime
	 * @param bisimulationTime
	 * @param lrtdpTime
	 * @param reward
	 */
	public void timeInfo (String _sInstanceName, Cronometro reachabilityTime, Cronometro bisimulationTime, Cronometro lrtdpTime, double reward, double valueFunctionS0, 
			boolean ONLY_BISIMULATION, boolean GET_NUMBER_OF_REACHABLE_STATES) {
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
	
	public void timeInfo(String folder, String _sInstanceName, double initialStateValue, Cronometro viTime, double reward) {
		StringBuffer timeInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo(
				timeInfoContent);
		timeInfoContent.append("INSTANCE=" + _sInstanceName + "\n");
		timeInfoContent.append("PLANNER_TIME="
				+ ((double) viTime.getTotalMilisegundos() / 1000.0d) + "\n");
		timeInfoContent.append("REWARD=" + reward + "\n");
		timeInfoContent.append("V*(s0)=" + initialStateValue + "\n");
		geradorDeArquivo.geraArquivo(folder + "/" + _sInstanceName + "_Time.txt");
	}
	
	///////////////////////////////////////////
	// Getters and setters.
	///////////////////////////////////////////

	public SieveOfEratosthenes getSoe() {
		return soe;
	}

	public void setSoe(SieveOfEratosthenes soe) {
		this.soe = soe;
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


	
}
