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

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
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
// import rddl.solver.mdp.rtdp.RTDPEnum.ProbState;
import rddl.solver.mdp.rtdp.off_LRTDPEnum.QUpdateResult;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Cronometro;
import util.GeradorDeArquivo;
import util.Pair;

public class off_sRTDP_feng_mejorado extends Policy {
	
	public static double SOLVER_TIME_LIMIT_PER_TURN = 86400.0d; // Solver time limit (seconds)
	public final static boolean SHOW_STATE   = true;
	public final static boolean SHOW_ACTIONS = true;
	public final static boolean SHOW_ACTION_TAKEN = true;
	
	
	// Only for diagnostics, comment this out when evaluating
	public final static boolean DISPLAY_SPUDD_ADDS_GRAPHVIZ = false;
	public final static boolean DISPLAY_SPUDD_ADDS_TEXT = false;
	private final static int VALUE = 1;
	private final static int REACHABILITY = 2;
	private static int GENERALIZATION_BY = REACHABILITY;
	private boolean USING_REACHABILITY_ANALYSIS = true;
	private static final int sRTDP = 1; // img e pre-img calculados dinamicamente
	private static final int sRTDP_2 = 2; // img calculada dinamicamente e pre-img calculada com base em probabilidade conjunta
	private static final int RTDP = 3;
	private static int ALGORITHM = sRTDP;
			
	
	public RDDL2Format _translation = null;
	
	// Using CString wrapper to speedup hash lookups
	public ADD _context;
	public ArrayList<Integer> _allMDPADDs;
	public ArrayList<CString> _alStateVars;
	public ArrayList<CString> _alPrimeStateVars;
	public ArrayList<CString> _alActionNames;
	public int _nContUpperUpdates; //For computing the number of value function updates
	public HashMap<CString, Action> _hmActionName2Action; // Holds transition function
	public ArrayList<Integer> _alSaveNodes; // Nodes to save during cache flushing
	
	// State variables
	public int _nRemainingHorizon = -1;
	
	// Just use the default random seed
	public Random _rand = new Random();
	public double base = 1.04648d;
	public Double _nPercError = 0.15d;
	public Double _nErrorGen = 0d;
	public int _nGetActions = 0;
	public Hashtable reduceRemapLeavesCache = new Hashtable();
	private Cronometro lrtdpTime;
	private ArrayList <Boolean> initialState;
	// Constructors
	public off_sRTDP_feng_mejorado() { }
	
	public off_sRTDP_feng_mejorado(String instance_name) {
		super(instance_name);
	}

	///////////////////////////////////////////////////////////////////////////
	//                      Main Action Selection Method
	///////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
		//System.out.println("FULL STATE:\n\n" + SPerseusSPUDDPolicy.getStateDescription(s));
		//SOLVER_TIME_LIMIT_PER_TURN = Math.pow(1.04, _nRemainingHorizon);
		// SOLVER_TIME_LIMIT_PER_TURN = Math.pow(base,base>=1?_nRemainingHorizon: _nHorizon- _nRemainingHorizon+1)/3;
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
		if (_nGetActions == 0) {
			lrtdpTime = new Cronometro();
			initialState = add_state_assign;
			lrtdpTime.setStart();
			doRTDP(SOLVER_TIME_LIMIT_PER_TURN, add_state_assign);
			lrtdpTime.setEnd();
		}
		
		QUpdateResult resultQ = null;
		resultQ = getBestQValue(add_state_assign);
		_csBestActionInitState = resultQ._csBestAction;
		
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
	
	public void timeInfo (Cronometro lrtdpTime, double reward) {
		StringBuffer timeInfoContent = new StringBuffer("");
		GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (timeInfoContent);
		timeInfoContent.append("INSTANCE=" + _sInstanceName + "\n");
		timeInfoContent.append("PLANNER_TIME=" + ((double) lrtdpTime.getTotalMilisegundos() / 1000.0d) + "\n");
		timeInfoContent.append("REWARD=" + reward + "\n");
		timeInfoContent.append("V*(s0)=" + _context.evaluate(_valueDD, initialState) + "\n");
		
		if (GENERALIZATION_BY == VALUE && !USING_REACHABILITY_ANALYSIS) {
			geradorDeArquivo.geraArquivo("offSRTDPValueTime\\" + _sInstanceName + "_Time.txt");
		}
		
		if (GENERALIZATION_BY == VALUE && USING_REACHABILITY_ANALYSIS) {
			geradorDeArquivo.geraArquivo("offReachSRTDPValueTime\\" + _sInstanceName + "_Time.txt");
		}
		
		if (GENERALIZATION_BY == REACHABILITY) {
			if (ALGORITHM == sRTDP) {
				geradorDeArquivo.geraArquivo("offSRTDPReachabilityImpl1Time\\" + _sInstanceName + "_Time.txt");
			} else if (ALGORITHM == sRTDP_2) {
				geradorDeArquivo.geraArquivo("offSRTDPReachabilityImpl2Time\\" + _sInstanceName + "_Time.txt");
			}
		}
	}
	
	public void roundEnd(double reward) {
		timeInfo (lrtdpTime, reward);
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
	public int _maxDD;
	public int _prevDD;
	public int _nDDType; // Type of DD to use
	public int _nTrials;
	public double _dRewardRange; // Important if approximating
	public double _dDiscount;
	public int _nHorizon;
	public CString _csBestActionInitState = null;
	public HashMap<Integer,Integer> _hmPrimeVarID2VarID;
	public HashMap<CString,Integer> _hmAct2Regr; // Cached DDs from last regression step
	public HashMap<String,String> _hmStringPrimeVarID2VarID;

	//V_E
	public int _nE;
	//V_E'
	public int _nEprime;
	//E' Masked
	public int _nMaskedEprime;
	//E U E' Masked
	public int _nMaskedEuEprime;
	//E Masked
	public int _nMaskedE;
	//-E Masked
	public int _nMaskedNE;
	//Aux
	public int _nAux;
	//Total
	public int _nTotal;
	
	// Initialize all variables (call before starting value iteration)
	public void resetSolver() {
		_prevDD = _maxDD = -1;
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
		_hmStringPrimeVarID2VarID = new HashMap<String, String>();
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
			_hmStringPrimeVarID2VarID.put(var_prime, var);			
			_hmStringPrimeVarID2VarID.put(var, var_prime);
		}
		
		_dRewardRange = -Double.MAX_VALUE;
		
		// OLD
		// for (Action a : _hmActionName2Action.values())
		//	_dRewardRange = Math.max(_dRewardRange, 
		//			_context.getMaxValue(a._reward) - 
		//	        _context.getMinValue(a._reward));
		
		for (Action a : _hmActionName2Action.values()) {
			_dRewardRange = Math.max(_dRewardRange,
			 _context.getMaxValue(a._reward));
			// _dRewardRange = Math.max(_dRewardRange,
			// 		_context.getMaxValue(a._reward));
			// maxReward = Math.max (maxReward, _context.getMaxValue(a._reward));
			// minReward = Math.min (minReward, _context.getMinValue(a._reward));
		}
		
		// IMPORTANT: RTDP needs **optimistic upper bound initialization**
		double value_range = (_dDiscount < 1d) 
			? _dRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
			: _nHorizon * _dRewardRange;        // assume max reward over horizon
		_valueDD = _context.getConstantNode(value_range);
		_nErrorGen = Math.abs(value_range*_nPercError);
		//base = timeInstance();
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
	
	public int computeJointProbability (Action action) {
		Integer jointProbability = _context.getConstantNode(1);
		LinkedHashSet <Integer> instanceFluents = new LinkedHashSet <Integer> ();
		for (int i = 1; i <= _context._hmID2VarName.size() / 2; i++) {
			instanceFluents.add(i);
		}
		LinkedHashSet<Integer> nextStateFluents = new LinkedHashSet(
				getNextStateFluents(instanceFluents));
		Iterator<Integer> nextStateFluentsIterator = nextStateFluents.iterator();
		int counter = 0;
		while (nextStateFluentsIterator.hasNext()) {
			Integer nextStateFluent = nextStateFluentsIterator.next();
			if (action._hmVarID2CPT.containsKey(nextStateFluent)) {
				HashMap <Double, Integer> oldValueToPrime = new HashMap<Double, Integer>();
				Integer head_var_gid = nextStateFluent;
				Integer cpt_dd = action._hmVarID2CPT.get(head_var_gid);
				System.out.println("|X'| = " +  _translation._context._hmID2VarName.get(nextStateFluent));
				jointProbability = _context.applyInt(jointProbability, cpt_dd, ADD.ARITH_PROD);
				// _context.getGraph(jointProbability).launchViewer();
			}
		}
		return jointProbability;
	}

	// Main RTDP Algorithm
	public void doRTDP(double time_limit_secs, ArrayList init_state) {

		System.out.println("RTDP: Time limit: " + _nTimeLimitSecs + 
				" seconds, discount: " + _dDiscount + ", horizon: " + 
				_nRemainingHorizon + "/" + _nHorizon);

		_nTimeLimitSecs = time_limit_secs;
		_lStartTime = System.currentTimeMillis();
		//CString best_action_init_state = null;
		Double previousInitStateValue = _context.evaluate(_valueDD, init_state);
		_prevDD = _valueDD;
		try {
			writeToLog(_sInstanceName);
			// Trial depth should be exactly equal to remaining horizon-to-go on this round
			_nTrials = 0;
			if (USING_REACHABILITY_ANALYSIS) {
				reachableStates = findReachableStates ((ArrayList <Boolean>) init_state, 40);
			}
			
			if (GENERALIZATION_BY == REACHABILITY) {
				statesSet = -1;
			}
			
			while(/*_nTrials<1){/*/true) {
				if (GENERALIZATION_BY == VALUE) {
					doValueSRTDPTrial(_nRemainingHorizon, init_state);
				} else if (GENERALIZATION_BY == REACHABILITY) {
					doReachabilitySRTDPTrial(_nRemainingHorizon, init_state);
				}
				_nTrials++;
				
				int diff = _context.applyInt(_valueDD, _prevDD, DD.ARITH_MINUS);
				double max_pos_diff = _context.getMaxValue(diff);
				double max_neg_diff = _context.getMinValue(diff);
				double max_diff = Math.max(Math.abs(max_pos_diff), Math.abs(max_neg_diff));
				
				
				// if (_nTrials > 1) {
				//	if (Math.abs(previousInitStateValue - _context.evaluate(_valueDD, init_state)) < 0.001d) {
				//		break;
				//	} else {
				//		previousInitStateValue = _context.evaluate(_valueDD, init_state);
				//	}
				// }
				if (max_diff < 0.001d) {
					break;
				} else {
					_prevDD = _valueDD;
				}
			}
			
		} catch (TimeOutException e) {
			System.out.println("RTDP: TIME LIMIT EXCEEDED after " + _nTrials + " trials.");
		} catch (IOException ioe) {
			System.out.println("Error in writing Log.");
		}  catch (Exception e) {
			System.err.println("RTDP: ERROR at " + _nTrials + " trials.");
			e.printStackTrace(System.err);
			System.exit(1);
		} catch (Throwable t) {
			if (t instanceof OutOfMemoryError) {
				StringBuffer timeInfoContent = new StringBuffer("");
				GeradorDeArquivo geradorDeArquivo = new GeradorDeArquivo (timeInfoContent);
				geradorDeArquivo.adiciona(new StringBuffer("INSTANCE=" + _sInstanceName));
				geradorDeArquivo.adiciona(new StringBuffer("RESULT=OUT_OF_MEMORY"));
				geradorDeArquivo.adiciona(new StringBuffer("PLANNER_TIME = " + (_lStartTime - System.currentTimeMillis())/1000.0d));
				
				if (GENERALIZATION_BY == VALUE && !USING_REACHABILITY_ANALYSIS) {
					geradorDeArquivo.geraArquivo("offSRTDPValueTime\\" + _sInstanceName + "_OutOfMemory.txt");
				}
				
				if (GENERALIZATION_BY == VALUE && USING_REACHABILITY_ANALYSIS) {
					geradorDeArquivo.geraArquivo("offReachSRTDPValueTime\\" + _sInstanceName + "_OutOfMemory.txt");
				}
				
				if (GENERALIZATION_BY == REACHABILITY) {
					geradorDeArquivo.geraArquivo("offSRTDPReachabilityTime\\" + _sInstanceName + "_OutOfMemory.txt");
				}
			}
		} finally {
			
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " + 
					_context.countExactNodes(_valueDD) + " nodes, best action: " + 
					_csBestActionInitState);
			
			// double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
			// try {
			//	writeToLog(instant+ "	"+_context.evaluate(_valueDD, init_state));
			// } catch (IOException e) {
				// TODO Auto-generated catch block
			//	e.printStackTrace();
			// }
		}
		
		
		
		// Return the best action for the initial state from the last completed trial
		//return best_action_init_state == null ? null : best_action_init_state._string;
	}
	private static final String LOG_FILE = "rddloffline";//"sRTDP_off";
	public void writeToLog(String msg) throws IOException {
		BufferedWriter bw = new BufferedWriter(new FileWriter(LOG_FILE + ".log" , true));
		bw.write(msg);
		bw.newLine();
		bw.flush();
		bw.close();
	}
	public boolean _app= true;
	
	Integer reachableStates, currentLayer, multCPTs, succss;
	private boolean LOG_CONVERGENCE = true;
	
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
	
	private int findReachableStates(ArrayList<Boolean> add_state_assign_clone, int horizon) {
		boolean debug = false;
		reachableStates = _context.getConstantNode(0);
		reachableStates = DDUtils.UpdateValue(_context, reachableStates, add_state_assign_clone, 1);
		currentLayer = DDUtils.UpdateValue(_context, reachableStates, add_state_assign_clone, 1);
		// _context.getGraph(reachableStates).launchViewer();
		System.out.println("Computing the reachable states set...");
		for (int i = 0; i < horizon; i++) {
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
 			if (nextLayer == currentLayer) {
 				System.out.println("All reachable states found.");
 				break;
 			}
 			currentLayer = nextLayer;
 			// flushCaches();
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
		// flushCaches();
		
		return reachableStates;
	}
	
	
	// Run a single RTDP trial, return best action as seen from initial state
	public void doValueSRTDPTrial(int trial_depth, ArrayList init_state) throws TimeOutException,IOException {
	
		//CString best_action_init_state = null;
		CString best_action = null;
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		// _context.getGraph(reachableStates).launchViewer();
		//ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>(_nTrials+3);
		for (int steps_to_go = 40; steps_to_go > 0; steps_to_go--) {
			
			//System.out.println("Forward step [" + steps_to_go + "]: " + cur_state);
			
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			ArrayList<Boolean> assign = new ArrayList<Boolean>();
			for (int i = 0; i <= _context._alOrder.size(); i++)
				assign.add(null);
			double val = _context.evaluate(_valueDD, cur_state);
			//_context.getGraph(_valueDD).launchViewer();		
			reduceRemapLeavesCache =  new Hashtable();
			_nMaskedE = reduceRemapLeaves(_valueDD, val+_nErrorGen, val-_nErrorGen);
			// _context.getGraph(_nMaskedE).launchViewer();				
			if (USING_REACHABILITY_ANALYSIS) {
				_nMaskedE = _context.applyInt(_nMaskedE, reachableStates, ADD.ARITH_PROD);
			}
			// _context.getGraph(_nMaskedE).launchViewer();
			_nMaskedEprime = _nMaskedE;
			computeSuccesors();
			//_context.getGraph(_nMaskedEprime).launchViewer();
			_nMaskedEuEprime = _context.applyInt(_nMaskedE, _nMaskedEprime, ADD.ARITH_SUM);
			reduceRemapLeavesCache =  new Hashtable();
			_nMaskedEuEprime = reduceRemapLeaves(_nMaskedEuEprime);
			// _context.getGraph(_nMaskedEuEprime).launchViewer();
			_nEprime = _context.applyInt(_nMaskedEprime, _valueDD, DD.ARITH_PROD);
			// _context.getGraph(_nEprime).launchViewer();
			UpdateAbstractState();
			//_context.getGraph(_nE).launchViewer();
			reduceRemapLeavesCache =  new Hashtable();
			_nMaskedNE = NegativeAdd(_nMaskedE);
			//_context.getGraph(_nMaskedNE).launchViewer();
			int VNE = _context.applyInt(_valueDD, _nMaskedNE, DD.ARITH_PROD);
			// Update Q-value			
			//_context.getGraph(_nE).launchViewer();
			//_context.getGraph(_nMaskedNE).launchViewer();
			_valueDD = _context.applyInt(_nE, VNE, DD.ARITH_SUM);
			//_context.getGraph(_valueDD).launchViewer();
			// Compute best action for current state (along with Q-value to backup)
			if (LOG_CONVERGENCE ) {
				if (cur_state.equals(init_state)){
					double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
					writeToLog(instant+ "	"+_context.evaluate(_valueDD, cur_state));
				}
			}
			QUpdateResult res = getBestQValue(cur_state);
			if (best_action == null) { // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
			}
			//System.out.println(res._dBestQValue + " "+ res._csBestAction);
			//DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			//_nContUpperUpdates++;
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
	
	HashMap <ArrayList <Boolean>, Integer> _hmStateToSetOfStates = new HashMap <ArrayList <Boolean>, Integer>();
	HashMap <Integer, Integer> _hmStateToImg = new HashMap <Integer, Integer> ();
	HashMap <Integer, Integer> _hmStatesToPreImg = new HashMap <Integer, Integer> ();
	Integer statesSet = -1;
	Integer statesOutOfImageOfS = -1;
	Integer abstractState = -1;
	Integer curStateSet = -1;
	Integer imgOfCurState = -1;
	Integer preImgOfCurStateImg = -1;
	HashMap <Action, Integer> actionJointProbabilities = null;
	
	Integer reachabilityGeneralization (ArrayList <Boolean> cur_state) {
		
		if ((curStateSet = _hmStateToSetOfStates.get(cur_state)) == null) {
			curStateSet = _context.getConstantNode(0.0d);
			curStateSet = DDUtils.UpdateValue(_context, curStateSet, cur_state, 1.0d);
			_hmStateToSetOfStates.put(cur_state, curStateSet);
		}
		
		// _context.getGraph(curStateSet).launchViewer();
		
		if (ALGORITHM == sRTDP) {
			if ((imgOfCurState = _hmStateToImg.get(curStateSet)) == null) {
				imgOfCurState = findReachableStates(cur_state, 1);
				_hmStateToImg.put(curStateSet, imgOfCurState);
			}
			
			// _context.getGraph(imgOfCurState).launchViewer();
				
			if ((preImgOfCurStateImg = _hmStatesToPreImg.get(imgOfCurState)) == null) {
				_hmStatesToPreImg.put(imgOfCurState, curStateSet);
				preImgOfCurStateImg = _hmStatesToPreImg.get(imgOfCurState);
			} else {
				preImgOfCurStateImg = _context.applyInt(_context.applyInt(curStateSet, preImgOfCurStateImg, ADD.ARITH_SUM), 
						 _context.applyInt(curStateSet, preImgOfCurStateImg, ADD.ARITH_PROD), ADD.ARITH_MINUS);
				_hmStatesToPreImg.put(imgOfCurState, preImgOfCurStateImg);
			}
			
			// _context.getGraph(preImgOfCurStateImg).launchViewer();
			
			if ((imgOfCurState != null) && (preImgOfCurStateImg != null)) {
				statesSet = _context.getConstantNode(1.0d);
				statesOutOfImageOfS = _context.applyInt(statesSet, imgOfCurState, ADD.ARITH_MINUS);
				// _context.getGraph(statesOutOfImageOfS).launchViewer();
				Integer preImgSMinusImgS = null;
				if ((preImgSMinusImgS = _hmStatesToPreImg.get(statesOutOfImageOfS)) == null) {
					preImgSMinusImgS = _context.getConstantNode(0.0d);
				}
				abstractState = _context.applyInt(preImgOfCurStateImg, preImgSMinusImgS, ADD.ARITH_MINUS);
				// _context.getGraph(abstractState).launchViewer();
			}
			return abstractState;
			
		} else if (ALGORITHM == sRTDP_2) {
			if (actionJointProbabilities == null) {
				actionJointProbabilities = new HashMap <Action, Integer>();
				for (CString a : _hmActionName2Action.keySet()) {
					Action action = _hmActionName2Action.get(a);
					Integer jointProbability = computeJointProbability(action);
					actionJointProbabilities.put(action, jointProbability);
				}
			}
			
			if ((imgOfCurState = _hmStateToImg.get(curStateSet)) == null) {
				imgOfCurState = findReachableStates(cur_state, 1);
				imgOfCurState = _context.remapGIDsInt (imgOfCurState, _hmStringPrimeVarID2VarID);
				// _context.getGraph(imgOfCurState).launchViewer();
				_hmStateToImg.put(curStateSet, imgOfCurState);
			}
			
			// _context.getGraph(imgOfCurState).launchViewer();
				
			if ((preImgOfCurStateImg = _hmStatesToPreImg.get(imgOfCurState)) == null) {
				preImgOfCurStateImg = _context.getConstantNode(0.0d);
				Integer preImgOfCurStateAndAction = null;
				for (CString a : _hmActionName2Action.keySet()) {
					Action action = _hmActionName2Action.get(a);
					// _context.getGraph(actionJointProbabilities.get(action)).launchViewer();
					preImgOfCurStateAndAction = _context.applyInt(imgOfCurState, actionJointProbabilities.get(action), ADD.ARITH_PROD);
					// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
					for (CString x : _alStateVars) {
						Integer xi = (Integer) _context._hmVarName2ID.get(x._string);
						String varName = (String) _context._hmID2VarName.get(xi);
						varName = varName + "'";
						Integer xiPrime = (Integer) _context._hmVarName2ID
								.get(varName);
						preImgOfCurStateAndAction = _context.opOut(preImgOfCurStateAndAction, xiPrime, DD.ARITH_SUM);
					}
					// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
					preImgOfCurStateAndAction = reduceRemapLeaves(preImgOfCurStateAndAction);
					// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
				
					preImgOfCurStateImg = _context.applyInt(_context.applyInt(preImgOfCurStateImg, preImgOfCurStateAndAction, ADD.ARITH_SUM),
															_context.applyInt(preImgOfCurStateImg, preImgOfCurStateAndAction, ADD.ARITH_PROD), ADD.ARITH_MINUS);
					// _context.getGraph(preImgOfCurStateImg).launchViewer();
				}
				// _context.getGraph(imgOfCurState).launchViewer();
				// _context.getGraph(preImgOfCurStateImg).launchViewer();
				_hmStatesToPreImg.put(imgOfCurState, preImgOfCurStateImg);
				preImgOfCurStateImg = _hmStatesToPreImg.get(imgOfCurState);
			} 
			
			// _context.getGraph(preImgOfCurStateImg).launchViewer();
			
			if ((imgOfCurState != null) && (preImgOfCurStateImg != null)) {
				statesSet = _context.getConstantNode(1.0d);
				statesOutOfImageOfS = _context.applyInt(statesSet, imgOfCurState, ADD.ARITH_MINUS);
				// _context.getGraph(statesOutOfImageOfS).launchViewer();
				Integer preImgSMinusImgS = null;
				if ((preImgSMinusImgS = _hmStatesToPreImg.get(statesOutOfImageOfS)) == null) {
					preImgSMinusImgS = _context.getConstantNode(0.0d);
					Integer partialPreImg = null;
					for (CString a : _hmActionName2Action.keySet()) {
						Action action = _hmActionName2Action.get(a);
						// _context.getGraph(actionJointProbabilities.get(action)).launchViewer();
						partialPreImg = _context.applyInt(statesOutOfImageOfS, actionJointProbabilities.get(action), ADD.ARITH_PROD);
						// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
						for (CString x : _alStateVars) {
							Integer xi = (Integer) _context._hmVarName2ID.get(x._string);
							String varName = (String) _context._hmID2VarName.get(xi);
							varName = varName + "'";
							Integer xiPrime = (Integer) _context._hmVarName2ID
									.get(varName);
							partialPreImg = _context.opOut(partialPreImg, xiPrime, DD.ARITH_SUM);
						}
						// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
						partialPreImg = reduceRemapLeaves(partialPreImg);
						// _context.getGraph(preImgOfCurStateAndAction).launchViewer();
						
						// System.out.println("\t\tRemapping GIDs...");
						// multCPTs = _context.remapGIDsInt (multCPTs, _hmStringPrimeVarID2VarID);
						
						
						preImgSMinusImgS = _context.applyInt(_context.applyInt(preImgSMinusImgS, partialPreImg, ADD.ARITH_SUM),
																_context.applyInt(preImgSMinusImgS, partialPreImg, ADD.ARITH_PROD), ADD.ARITH_MINUS);
						// _context.getGraph(preImgOfCurStateImg).launchViewer();
					}
					
					_hmStatesToPreImg.put(statesOutOfImageOfS, preImgSMinusImgS);
					preImgSMinusImgS = _hmStatesToPreImg.get(statesOutOfImageOfS);
				} 
				// _context.getGraph(preImgOfCurStateImg).launchViewer();
				// _context.getGraph(preImgSMinusImgS).launchViewer();
				abstractState = _context.applyInt(preImgOfCurStateImg, preImgSMinusImgS, ADD.ARITH_MINUS);
				// _context.getGraph(abstractState).launchViewer();
				abstractState = reduceRemapLeaves(abstractState);
			}
			return abstractState;
		} else {
			return curStateSet;
		}
	}
	

	
	public void doReachabilitySRTDPTrial(int trial_depth, ArrayList init_state) throws TimeOutException,IOException {
		
		//CString best_action_init_state = null;
		CString best_action = null;
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList cur_state = init_state;
		// _context.getGraph(reachableStates).launchViewer();
		//ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>(_nTrials+3);
		for (int steps_to_go = 40; steps_to_go > 0; steps_to_go--) {
			
			//System.out.println("Forward step [" + steps_to_go + "]: " + cur_state);
			
			// Flush caches and check time limit
			// flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			ArrayList<Boolean> assign = new ArrayList<Boolean>();
			for (int i = 0; i <= _context._alOrder.size(); i++)
				assign.add(null);
			
			_nMaskedE = reachabilityGeneralization(cur_state);
			// _context.getGraph(_nMaskedE).launchViewer();
			// reduceRemapLeavesCache =  new Hashtable();
			// _nMaskedE = reduceRemapLeaves(_nMaskedE);
			// _context.getGraph(_nMaskedE).launchViewer();
			
			
			// _nMaskedE = reduceRemapLeaves(_valueDD, val+_nErrorGen, val-_nErrorGen);
			// _nMaskedE = PreImg(Img(s)) - PreImg(S - Img(s));
			
			_nMaskedEprime = _nMaskedE;
			computeSuccesors();
			
			// _context.getGraph(_nMaskedEprime).launchViewer();
			
			_nMaskedEuEprime = _context.applyInt(_nMaskedE, _nMaskedEprime, ADD.ARITH_SUM);
			reduceRemapLeavesCache =  new Hashtable();
			_nMaskedEuEprime = reduceRemapLeaves(_nMaskedEuEprime);
			// _context.getGraph(_nMaskedEuEprime).launchViewer();
			_nEprime = _context.applyInt(_nMaskedEprime, _valueDD, DD.ARITH_PROD);
			// _context.getGraph(_nEprime).launchViewer();
			UpdateAbstractState();
			// _context.getGraph(_nE).launchViewer();
			_nE = _context.applyInt(_nE, _nMaskedE, ADD.ARITH_PROD);
			// _context.getGraph(_nE).launchViewer();
			
			reduceRemapLeavesCache =  new Hashtable();
			_nMaskedNE = NegativeAdd(_nMaskedE);
			//_context.getGraph(_nMaskedNE).launchViewer();
			int VNE = _context.applyInt(_valueDD, _nMaskedNE, DD.ARITH_PROD);
			// _context.getGraph(_nMaskedNE).launchViewer();
			// Update Q-value			
			//_context.getGraph(_nE).launchViewer();
			//_context.getGraph(_nMaskedNE).launchViewer();
			_valueDD = _context.applyInt(_nE, VNE, DD.ARITH_SUM); // V_E + V_{E'}^{copy}
			// _context.getGraph(_valueDD).launchViewer();
			// Compute best action for current state (along with Q-value to backup)
			if (LOG_CONVERGENCE) {
				if (cur_state.equals(init_state)){
					double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
					writeToLog(instant+ "	"+_context.evaluate(_valueDD, cur_state));
				}
			}
			QUpdateResult res = getBestQValue(cur_state);
			if (best_action == null) { // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
			}
			//System.out.println(res._dBestQValue + " "+ res._csBestAction);
			//DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			//_nContUpperUpdates++;
			// Sample next state
			cur_state = sampleNextState(cur_state, res._csBestAction); // s = execute (s,a)
		}
	}
	
	private void computeSuccesors() {
		Integer xiprime, xi;
		_nAux = _nMaskedEprime;
		_nTotal = _context.getConstantNode(0d);
		for (int i = 0; i < _alActionNames.size(); i++){
			CString actionname=_alActionNames.get(i);			
			Action a = _hmActionName2Action.get(actionname);
			HashMap<Integer, Integer> iD2ADD = a._hmVarID2CPT;
			_nMaskedEprime = _nAux;
			for (CString x : _alStateVars){		
				xiprime=(Integer)_context._hmVarName2ID.get(_translation._hmPrimeRemap.get(x._string));
				Integer cpt_a_xiprime = iD2ADD.get(xiprime);			
				reduceRemapLeavesCache = new Hashtable();
				Integer succss = reduceRemapLeaves(cpt_a_xiprime);
				_nMaskedEprime = _context.applyInt(_nMaskedEprime, succss, ADD.ARITH_PROD);
				flushCaches();
			}
			
			for (CString x : _alStateVars){		
				xi =(Integer)_context._hmVarName2ID.get(x._string);
				_nMaskedEprime = _context.opOut(_nMaskedEprime, xi, ADD.ARITH_SUM);
				flushCaches();
			}
			
			_nMaskedEprime = _context.remapGIDsInt(_nMaskedEprime, _hmStringPrimeVarID2VarID);			
			_nTotal = _context.applyInt(_nTotal, _nMaskedEprime, ADD.ARITH_SUM);
			reduceRemapLeavesCache = new Hashtable();
			_nTotal = reduceRemapLeaves(_nTotal);
			flushCaches();
		}
		
		_nMaskedEprime = _nTotal;
		_nTotal =  _context.getConstantNode(0d);
		_nAux =  _context.getConstantNode(0d);
		flushCaches();
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
	public QUpdateResult getBestQValue(ArrayList cur_state) {
		
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
	public double getQValue(int prime_vfun, ArrayList cur_state, CString action) {
		
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
		// System.out.println("Flush Caches executing...");

		_context.clearSpecialNodes();
		for (Integer dd : _alSaveNodes)
			_context.addSpecialNode(dd);
		for (Integer dd : _allMDPADDs)
			_context.addSpecialNode(dd);
		_context.addSpecialNode(_nE);
		_context.addSpecialNode(_nEprime);
		_context.addSpecialNode(_nMaskedEprime);
		_context.addSpecialNode(_nMaskedEuEprime);
		_context.addSpecialNode(_nMaskedE);
		_context.addSpecialNode(_nMaskedNE);
		_context.addSpecialNode(_valueDD);
		_context.addSpecialNode(_nAux);
		_context.addSpecialNode(_nTotal);
		
		if ((curStateSet != null) && (curStateSet != -1)) {
			_context.addSpecialNode(curStateSet);
		}
		
		if ((imgOfCurState != null) && (imgOfCurState != -1)) {
			_context.addSpecialNode(imgOfCurState);
		}
		
		if ((preImgOfCurStateImg != null) && (preImgOfCurStateImg != -1)) {
			_context.addSpecialNode(preImgOfCurStateImg);
		}
			
		if ((statesSet != null) && (statesSet != -1)) {
			_context.addSpecialNode(statesSet);
		}
		
		if ((statesOutOfImageOfS != null) && (statesOutOfImageOfS != -1)) {
			_context.addSpecialNode(statesOutOfImageOfS);
		}
		
		if ((abstractState != null) && (abstractState != -1)) {
			_context.addSpecialNode(abstractState);
		}
		
		for (Integer state : _hmStateToImg.keySet()) {
			_context.addSpecialNode(state);
			if (_hmStateToImg.get(state) != null) {
				_context.addSpecialNode(_hmStateToImg.get(state));
			}
		}
		
		for (Integer states : _hmStatesToPreImg.keySet()) {
			_context.addSpecialNode(states);
			if (_hmStatesToPreImg.get(states) != null) {
				_context.addSpecialNode(_hmStatesToPreImg.get(states));
			}
		}
		
		if (GENERALIZATION_BY == REACHABILITY) {
			if (ALGORITHM == sRTDP_2) {
				for (CString a : _hmActionName2Action.keySet()) {
					Action action = _hmActionName2Action.get(a);
					Integer jointProbabilityForA = actionJointProbabilities.get(action);
					if (jointProbabilityForA != null && jointProbabilityForA != -1) {
						_context.addSpecialNode(jointProbabilityForA);
					}
				}
			}
		}
		
		if (USING_REACHABILITY_ANALYSIS) {
			_context.addSpecialNode(reachableStates);
			_context.addSpecialNode(currentLayer);
		}
		if (_maxDD != -1)
			_context.addSpecialNode(_maxDD);
		if (_prevDD != -1)
			_context.addSpecialNode(_prevDD);
		
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
	
	public void UpdateAbstractState() throws TimeOutException {
		// Cache maintenance
		flushCaches();
		// Prime the value function
		_nEprime = _context.remapGIDsInt(_nEprime, _translation._hmPrimeRemap);
		// _context.getGraph(_nEprime).launchViewer();
		// Cache maintenance -- clear out previous nodes, but save Q-functions
		clearSaveNodes();
		//if (_hmAct2Regr != null) // Save previous regression (needed if time out)
			//for (CString a : _alActionNames)
				//saveNode(_hmAct2Regr.get(a));
		//////////////////////////////////////////////////////////////
		// Iterate over each action to obtain Q-function from _valueDD
		//////////////////////////////////////////////////////////////
		_maxDD = -1;
		HashMap<CString,Integer> temp_regr = new HashMap<CString,Integer>();
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			CString action_name = me.getKey();
			Action a = me.getValue();
			//////////////////////////////////////////////////////////////
			// Regress the current value function through each action
			//////////////////////////////////////////////////////////////
			int regr = regress(_nEprime, a, true);
			//_context.getGraph(_nEprime).launchViewer();
			//temp_regr.put(action_name, regr);
			// Cache maintenance - after regression
			saveNode(regr); // Save latest Q-function regression
			flushCaches();
			//checkTimeLimit();
			//////////////////////////////////////////////////////////////
			// Take the max over this action and the previous action
			//////////////////////////////////////////////////////////////
			_maxDD = (_maxDD == -1? regr: _context.applyInt(_maxDD, regr, DD.ARITH_MAX));
			// Cache maintenance - after maximization
			flushCaches();
			//checkTimeLimit();
		}
		// We've done a full update of value DD, increment iteration counter
		// and update the cached Q-functions with the new ones
		_nE = _maxDD;
		// _context.getGraph(_valueDD).launchViewer();
		//_hmAct2Regr = temp_regr;		
	}
	
	// Compute and return the Q-function from vfun for action a
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
			int cpt_dd_restrictedEuEprime = _context.applyInt(cpt_dd, _nMaskedE, DD.ARITH_PROD);
			dd_ret = _context.applyInt(dd_ret, cpt_dd_restrictedEuEprime, DD.ARITH_PROD);
			saveNode(dd_ret);
			flushCaches();
			//checkTimeLimit();
			///////////////////////////////////////////////////////////////////
			// Sum out next state variable
			///////////////////////////////////////////////////////////////////
			clearSaveNode(dd_ret);
			dd_ret = _context.opOut(dd_ret, head_var_gid, DD.ARITH_SUM);
			saveNode(dd_ret);
			flushCaches();
			//checkTimeLimit();
		}
		// Discount the regressed function (if needed)
		if (_dDiscount < 1d)
			dd_ret = _context.scalarMultiply(dd_ret, _dDiscount);
		// Add in action-dependent reward
		int rewardrestrictectE = _context.applyInt(a._reward, _nMaskedE, DD.ARITH_PROD);
		dd_ret = _context.applyInt(dd_ret, rewardrestrictectE, DD.ARITH_SUM);
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
    		else{// find terminal node in the finalMap
    			ADDDNode leaf = (ADDDNode) nodeKey;
				Double value = leaf._dLower;
    			if (value > 0d)
    				return _context.getConstantNode(1d);
    			else
    				return _context.getConstantNode(0d);
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
	private int reduceRemapLeaves(int id, double max, double min) {
		Integer Fr= (Integer)reduceRemapLeavesCache.get(id);
    	if(Fr==null){
    		ADDNode nodeKey=_context.getNode(id);
    		if(nodeKey instanceof ADDINode){
	    		Integer Fh=reduceRemapLeaves(((ADDINode)nodeKey)._nHigh, max, min);
	    		Integer Fl=reduceRemapLeaves(((ADDINode)nodeKey)._nLow, max, min);
	    		Integer Fvar= ((ADDINode)nodeKey)._nTestVarID;
	    		Fr=_context.getINode(Fvar,Fl,Fh, true);
	    		reduceRemapLeavesCache.put(id, Fr);
	    	}
    		else{// find terminal node in the finalMap
    			ADDDNode leaf = (ADDDNode) nodeKey;
				Double value = leaf._dLower;
    			if (value >= min && value <= max)
    				return _context.getConstantNode(1d);
    			else
    				return _context.getConstantNode(0d);
    		}
    	}
    	return Fr;
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
