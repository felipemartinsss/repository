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

package rddl.solver.mdpst.rtdp;

import graph.Graph;

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
import rddl.solver.mdp.rtdp.RTDPEnumFelipe.ProbState;
import rddl.translate.RDDL2Format;
import util.CString;
import util.Pair;

public class RTDPEnumSTLinear extends Policy {
	
	public static int SOLVER_TIME_LIMIT_PER_TURN = 2; // Solver time limit (seconds)
	
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
	
	// State variables
	public int _nRemainingHorizon = -1;
	
	private double heuristicaAdmissivel = 0d;
	
	// Variável utilizada para contaminar a distribuição de probabilidades gerando o MDPST.
	private double epsilon = 0.1; 
	
	// Just use the default random seed
	public Random _rand = new Random();
		
	// Constructors
	public RTDPEnumSTLinear() { }
	
	public RTDPEnumSTLinear(String instance_name) {
		super(instance_name);
	}
	
	/**
	 * Classe interna que representa um conjunto de estados alcançáveis e possui uma
	 * massa de probabilidade desse conjunto ser alcançado.
	 * @author Felipe
	 *
	 */
	public static class ProbSet {
		private HashSet <ArrayList <Boolean>> statesIn;
		private double probability;
		
		public ProbSet () {
			statesIn = new HashSet <ArrayList <Boolean>> ();
			probability = 0.0d;
		}
		
		public ProbSet (HashSet <ArrayList <Boolean>> statesIn, double probability) {
			this.statesIn = statesIn;
			this.probability = probability;
		}
		
		public double getProbability() {
			return probability;
		}
		
		public HashSet <ArrayList <Boolean>> getStatesIn() {
			return statesIn;
		}
		
		public void setProbability (double probability) {
			this.probability = probability;
		}
		
		public void setStatesIn (HashSet <ArrayList <Boolean>> statesIn) {
			this.statesIn = statesIn;
		}
		
		public boolean addState (ArrayList <Boolean> state) {
			return (statesIn.add (state));
		}
		
		public String toString() {
			StringBuffer probSetAsString = new StringBuffer("P ({");
			Iterator <ArrayList<Boolean>> stateIterator = statesIn.iterator();
			while (stateIterator.hasNext()) {
				ArrayList <Boolean> state = stateIterator.next();
				probSetAsString.append(state.toString());
				if (stateIterator.hasNext()) {
					probSetAsString.append(", ");
				}
			}
			probSetAsString.append("} = " + probability);
			return probSetAsString.toString();
		}
	}

	public static class ProbState implements Comparable {
		public double  _dProb;
		public ArrayList<Boolean> _alState;
		public ProbState(double Prob, ArrayList<Boolean> State) {
			_dProb = Prob;
			_alState = State;
		}
		public String toString(){
			return _alState.toString();
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
	///////////////////////////////////////////////////////////////////////////
	//                      Main Action Selection Method
	///////////////////////////////////////////////////////////////////////////

	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
		//System.out.println("FULL STATE:\n\n" + SPerseusSPUDDPolicy.getStateDescription(s));

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
		ArrayList<Boolean> add_state_assign = DDUtils.ConvertTrueVars2DDAssign(_context, true_vars, _alStateVars);
		_csBestActionInitState = null;
		doRTDP(SOLVER_TIME_LIMIT_PER_TURN, add_state_assign);
		String action_taken = (_csBestActionInitState == null ? null : _csBestActionInitState._string);
		if (action_taken == null) {
			// No RTDP results available, just take random action
			ArrayList<String> actions = new ArrayList<String>(action_map.keySet());
			action_taken = actions.get(_rand.nextInt(actions.size()));
			if (SHOW_ACTION_TAKEN) {
				System.out.println("\n--> [Random] action taken: " + action_taken);
			}
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
					int dd = _translation._var2transDD.get(new Pair<String, String>(a, s));
					
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
	public int  _nTimeLimitSecs;
	public static Runtime RUNTIME = Runtime.getRuntime();

	// Local vars
	public INSTANCE _rddlInstance = null;
	public HashMap <ArrayList<Boolean>, Double> _valueDD;
	public int _nDDType; // Type of DD to use
	public int _nTrials;
	public double _dRewardRange; // Important if approximating
	public double _dDiscount;
	public int _nHorizon;
	public CString _csBestActionInitState = null;
	public HashMap<Integer,Integer> _hmPrimeVarID2VarID;
	public HashMap<ArrayList,HashMap<CString,Double>> _hmReward;
	

	// Initialize all variables (call before starting value iteration)
	public void resetSolver() {
		_nTrials = -1;
		_rddlInstance = _rddl._tmInstanceNodes.get(this._sInstanceName);
		if (_rddlInstance == null) {
			System.err.println("ERROR: Could not fine RDDL instance '" + _rddlInstance + "'");
			System.exit(1);
		}
		_dDiscount = _rddlInstance._dDiscount;
		if (_dDiscount == 1d) {
			_dDiscount = 0.99d;
		}
		_nHorizon  = _rddlInstance._nHorizon;
		
		// In RTDP we need to map from CPT head var (primed) into non-prime state variable
		_hmPrimeVarID2VarID = new HashMap<Integer,Integer>();
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
		}
		_hmReward = new HashMap<ArrayList,HashMap<CString,Double>>();
		
		_dRewardRange = 0d;
		for (Action a : _hmActionName2Action.values())
			_dRewardRange = Math.max(_dRewardRange, 
					_context.getMaxValue(a._reward) - 
			        _context.getMinValue(a._reward));
		
		 // IMPORTANT: RTDP needs **optimistic upper bound initialization**
		 heuristicaAdmissivel = (_dDiscount < 1d) 
		 	? _dRewardRange / (1d - _dDiscount) // being lazy: assume infinite horizon
		  	: _nHorizon * _dRewardRange;        // assume max reward over horizon*/
		
		System.out.println("Heuristica Admissivel: " + heuristicaAdmissivel);
		
		/*
		for (Action a : _hmActionName2Action.values()) {
			int maxRewardDD = _context.getConstantNode(_context.getMax(a._reward));
			a._reward = _context.applyInt(a._reward, maxRewardDD, _context.ARITH_MINUS);
			// _context.getGraph(a._reward).launchViewer();
		}*/
			
		//_valueDD = _context.getConstantNode(value_range);
		_valueDD =  new HashMap<ArrayList<Boolean>, Double>();
	}

	// Main RTDP Algorithm
	public void doRTDP(int time_limit_secs, ArrayList<Boolean> init_state) {

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
				doRTDPTrial(20, init_state);
				_nTrials++;
			}
		} catch (TimeOutException e) {
			System.out.println("RTDP: TIME LIMIT EXCEEDED after " + _nTrials + " trials.");
		} catch (Exception e) {
			System.err.println("RTDP: ERROR at " + _nTrials + " trials.");
			e.printStackTrace(System.err);
			System.exit(1);
		} finally {
			System.out.println("RTDP: Vfun at trial " + _nTrials + ": " /*+ 
					/*_context.countExactNodes(_valueDD) + " nodes, best action: " + 
					_csBestActionInitState*/);
		}
		
		// Return the best action for the initial state from the last completed trial
		//return best_action_init_state == null ? null : best_action_init_state._string;
	}
	
	// Run a single RTDP trial, return best action as seen from initial state
	public void doRTDPTrial(int trial_depth, ArrayList<Boolean> init_state) throws TimeOutException {
	
		//CString best_action_init_state = null;
		CString best_action = null;
		////////////////////////////////////////////////////////////////////////////
		// Simulate a trial from here to the horizon (updating along the way), then 
		// backtrack and update in reverse.
		////////////////////////////////////////////////////////////////////////////
		ArrayList<Boolean> cur_state = init_state;
		
		
		ArrayList<ArrayList> visited_states = new ArrayList<ArrayList>(trial_depth);
		for (int steps_to_go = trial_depth; steps_to_go > 0; steps_to_go--) {
			// System.out.println("Estado visitado: " + cur_state);
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			visited_states.add(cur_state);
			
			// Compute best action for current state (along with Q-value to backup)
			QUpdateResult res = getBestQValue(cur_state);
			if (best_action == null){ // first time through will update
				_csBestActionInitState = res._csBestAction;
				best_action = _csBestActionInitState;
				// System.out.println("Best Action: " + best_action + " -> Q = " + res._dBestQValue);
			}
			
			// Update Q-value
			//_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			_valueDD.put(cur_state, res._dBestQValue);
			_nContUpperUpdates++;
			// Sample next state
			cur_state = SortearEstado (res._alProbSets);
			// System.out.println("Estado atual: " + cur_state);
		}
		
		// Do final updates *in reverse* on return
		for (int depth = visited_states.size() - 1; depth >= 0; depth--) {
			// Flush caches and check time limit
			flushCaches(); // Only thing to keep is MDP def. and current vfun
			checkTimeLimit();
			//System.out.println("pasa el segundo");
			cur_state = visited_states.get(depth);
			// Update Q-value for each state
			QUpdateResult res = getBestQValue(cur_state);
			//_valueDD = DDUtils.UpdateValue(_context, _valueDD, cur_state, res._dBestQValue);
			_valueDD.put(cur_state, res._dBestQValue);
			_nContUpperUpdates++;
			// If back to initial state then update best action
			if (depth == 0) {
				_csBestActionInitState = res._csBestAction;
			}
		}

		// All of the RTDP updates were just to find out best action from initial state
		// (as a byproduct, we've updated the value function via asychronous DP for
		//  reuse on the next step of this trial and other trials)
		//return best_action_init_state;
	}
	
	public static class QUpdateResult {
		public CString _csBestAction;
		public double  _dBestQValue;
		public ArrayList<ProbSet> _alProbSets;
		public QUpdateResult(CString best_action, double best_qvalue, ArrayList<ProbSet> ProbSets) {
			_csBestAction = best_action;
			_dBestQValue  = best_qvalue;
			_alProbSets = ProbSets;
		}
	}

	// Find best Q-value/action for given state
	public QUpdateResult getBestQValue(ArrayList<Boolean> cur_state) {		
		QUpdateResult result = new QUpdateResult (null, Double.MIN_VALUE, new ArrayList<ProbSet>()); 
		for (Map.Entry<CString, Action> me : _hmActionName2Action.entrySet()) {
			Action a = me.getValue();
			Pair<Double, ArrayList<ProbSet>> qValue = getQValue(cur_state, a._csActionName);
			if (result._csBestAction == null || qValue._o1 > result._dBestQValue) { 
				result._csBestAction = a._csActionName;
				result._dBestQValue = qValue._o1;
				result._alProbSets =  qValue._o2;
			}
			//System.out.println("- " +a._csActionName + "(" + qvalue + ")");
		}
		//System.out.println("=> " + result._csBestAction + "(" + result._dBestQValue + ")");
		return result;
	}
	
	public static void verificaProbState (ArrayList <ProbState> probStates) {
		for (int i = 0; i < probStates.size(); i++) {
			if (probStates.get(i)._dProb > 1.0d) {
				System.out.println("Probabilidades extraidas incorretamente. Exemplo:");
				System.out.print ("Estado: " + probStates.get(i)._alState);
				System.out.println(" (Probabilidade = " + probStates.get(i)._dProb + ")");
				System.out.println("Encerrar aplicação.");
				System.exit(0);
			}
		}
	}
	
	public static void verificaProbSet (ArrayList <ProbSet> probSet) {
		for (int i = 0; i < probSet.size(); i++) {
			if (probSet.get(i).getProbability() > 1.0d) {
				System.out.println("Probabilidades geradas incorretamente. Exemplo:");
				System.out.print ("Conjunto: " + probSet.get(i).getStatesIn());
				System.out.println(" (Probabilidade = " + probSet.get(i).getProbability() + ")");
				System.out.println("Encerrar aplicação.");
				System.exit(0);
			}
		}
	}
	
	public static void imprimeProbState (ArrayList <ProbState> probStates) {
		for (int i = 0; i < probStates.size(); i++) {
			System.out.print ("Estado: " + probStates.get(i)._alState);
			System.out.println(" (Probabilidade = " + probStates.get(i)._dProb + ")");
		}
	}
	
	public static ArrayList <ProbSet> contaminacaoEpsilon (ArrayList <ProbState> probStates, double epsilon) {
		ArrayList <ProbSet> probSets = new ArrayList <ProbSet> ();
		double epsilonComplement = 1.0d - epsilon;
		ProbSet aux = new ProbSet();
		for (int i = 0; i < probStates.size(); i++) {
			ProbSet currentProbSet = new ProbSet ();
			currentProbSet.addState (probStates.get(i)._alState);
			currentProbSet.setProbability (probStates.get(i)._dProb * epsilonComplement);
			aux.addState (probStates.get(i)._alState);
			probSets.add(currentProbSet);
		}
		aux.setProbability(epsilon);
		probSets.add(aux);
		return probSets;
	}

	// Find Q-value for action in given state
	public Pair<Double, ArrayList<ProbSet>> getQValue (ArrayList<Boolean> currentState, CString action) {
		
		Action a = _hmActionName2Action.get(action);
		//keys = new HashMap<ArrayList<Boolean>, Integer>();
		ArrayList<ProbState> probStates = computeSuccesorsProbEnum(currentState, a._hmVarID2CPT);
		
		verificaProbState (probStates);
		
		ArrayList <ProbSet> probSets = contaminacaoEpsilon (probStates, epsilon);
		
		verificaProbSet (probSets);
		
		// System.out.println (probSets);
		
		// System.out.println("ProbStates for Action: " + action + " " + ProbsStates);
		//////////////////////////////////////////////////////////////
		// For each next-state in DBN for action 'a'
		//////////////////////////////////////////////////////////////
		double soma = 0.0d;
		
		
		if (!_valueDD.containsKey(currentState)) {
			// _valueDD.put(currentState, _context.evaluate(a._reward, currentState));
			_valueDD.put(currentState, heuristicaAdmissivel);
		}
		
		for (int indice = 0; indice < probSets.size(); indice++) {
			ProbSet reachableSet = probSets.get(indice);
			
			Iterator <ArrayList <Boolean>> stateIterator = reachableSet.getStatesIn().iterator();
			while (stateIterator.hasNext()) {
				ArrayList <Boolean> reachableState = stateIterator.next();
				
				if (!_valueDD.containsKey(reachableState)) {
				 	// _valueDD.put(reachableState, _context.evaluate(a._reward, reachableState));
					_valueDD.put(reachableState, heuristicaAdmissivel);
				}
			}
			
			
			double nextSetValue;
			stateIterator = reachableSet.getStatesIn().iterator();
			if (stateIterator.hasNext()) {
				ArrayList <Boolean> reachableState = stateIterator.next();
				nextSetValue = _valueDD.get(reachableState);
				while (stateIterator.hasNext()) {
					reachableState = stateIterator.next();
					// the nature always choices the worst value for the agent (MDPST) - Max Min
					if (_valueDD.get(reachableState) < nextSetValue) {
						nextSetValue = _valueDD.get(reachableState);
					}
				}
			
				double prob = reachableSet.getProbability();
				// System.out.print("(Pr = " + prob + ") * (" + valorEstadoSeguinte + ") ");
				soma += (prob * nextSetValue);
			}
		}
		
		// Get action-dependent reward
		double reward = 0;
		if (_hmReward.containsKey(currentState) && _hmReward.get(currentState).containsKey(action)) {
			reward = _hmReward.get(currentState).get(action);
		} else {
			reward = _context.evaluate(a._reward, currentState);
		}
		// Return regressed value for current state
		
		// System.out.println("*" + _dDiscount + " + " + reward);
		// System.out.println(reward + " + " + _dDiscount + " * " + soma + " = " + (reward + _dDiscount * soma));
		return new Pair <Double, ArrayList<ProbSet>> (reward + _dDiscount * soma,  probSets);
	}

	// For now we assume that the ADD transition functions for all
	// actions apply in every state... will have to revisit this later
	// w.r.t. RDDL's state-action constraints
	public ArrayList<Boolean> sampleNextState(ArrayList<Boolean> current_state, CString action) {
		
		Action a = _hmActionName2Action.get(action);
		ArrayList<Boolean> next_state = (ArrayList<Boolean>)current_state.clone(); // ensure correct size
		
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
		//_context.addSpecialNode(_valueDD);

		
		_context.flushCaches(true);
	}
	
	private ArrayList<ProbState> computeSuccesorsProbEnum(ArrayList<Boolean> state, HashMap<Integer, Integer> iD2ADD) {
		Integer multCPTs = _context.getConstantNode(1d);
		Integer xiprime;
		
		for (CString x : _alStateVars) {		
			xiprime = (Integer)_context._hmVarName2ID.get(_translation._hmPrimeRemap.get(x._string));
			Integer cpt_a_xiprime = iD2ADD.get(xiprime);
			double probTrue, probFalse;
			int levelprime = (Integer)_context._hmGVarToLevel.get(xiprime);
			if (state == null) {
				System.out.println("Estado seguinte = null");
			}
			
			state.set(levelprime, true);
			probTrue = _context.evaluate(cpt_a_xiprime,state);
			state.set(levelprime, null);
			probFalse = 1 - probTrue;
			Integer Fh = _context.getConstantNode(probTrue);
			Integer Fl = _context.getConstantNode(probFalse);
			Integer newCPT = _context.getINode (xiprime, Fl, Fh, true);
			multCPTs = _context.applyInt(multCPTs, newCPT, ADD.ARITH_PROD);
		}
		
		ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		ArrayList<Boolean> assign = new ArrayList<Boolean>();
		for (int i = 0; i <= _context._alOrder.size(); i++)
			assign.add(null);
		inOrderSearch(_context.getNode(multCPTs), assign, alEstadoProb);
		// _context.getGraph(multCPTs).launchViewer();
		// alEstadoProb.get(0)._dProb = 1;
		alEstadoProb = normaliza (alEstadoProb);
		return alEstadoProb;
	}
	
	private ArrayList<ProbState> normaliza(ArrayList<ProbState> alEstadoProb) {
		double soma = 0.0d;
		for (int i = 0; i < alEstadoProb.size(); i++) {
			soma += alEstadoProb.get(i)._dProb;
		}
		
		for (int i = 0; i < alEstadoProb.size(); i++) {
			alEstadoProb.get(i)._dProb /= soma;
		}
		
		return alEstadoProb;
	}

	/**
	 * Recebe um ID de um ADD e devolve uma HashMap com
	 * os estados que podem ser alcanÃ§ados pela aÃ§Ã£o representada por esse ADD
	 * @param idADD
	 */
	/*public ArrayList<ProbState> extraiProbabilidades (Integer idADD, HashMap<ArrayList<Boolean>, Integer> keys){
		ADDNode raiz = _context.getNode(idADD);
		ArrayList<ProbState> alEstadoProb = new ArrayList<ProbState>();
		
		ArrayList <Boolean> assign = new ArrayList <Boolean>();
		
		System.out.println ("Tamanho:" + _context._alOrder.size());
		// Initialize assignments
		for (int i = 0; i <= _context._alOrder.size(); i++) {
			assign.add(null);
		}
		
		if (raiz != null) 
			inOrderSearch(raiz, assign, alEstadoProb);
		//System.out.println("Busca inorder encerrada.");
		// NÃºmero de mapeamentos (estado, probabilidade).
		//System.out.println("ArrayList size: " + alEstadoProb.size());
		return alEstadoProb;
	}*/
	
	/**
	 * Realiza uma busca InOrder (Esquerda-Raiz-Direita) na Ã¡rvore e adiciona
	 * um par (Estado, Probabilidade) em uma HashMap sempre que uma folha
	 * da Ã¡rvore Ã© alcanlÃ§ada.
	 * @param node 
	 * @param s
	 * @param alEstadoProb
	 */
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
					
					System.out.println("Assign: " + assign + " = " + probabilidade);
					
					ProbState novoNo = new ProbState (probabilidade, newAssign);
					alEstadoProb.add(novoNo);
				}
			}
		}
	}
	
	/* Recebe uma lista de estados representados por ArrayList<Boolean> e recupera para cada um deles
	 * a probabilidade de ser alcanÃ§ado.
	 */
	public void imprimeEstadosAlcancaveis (ArrayList<ProbState> alEstadoProb) {
		Double probabilidadeTotal = 0.0d;
		for ( ProbState s : alEstadoProb) {
			System.out.println (s._alState + " = " + s._dProb);
			probabilidadeTotal += s._dProb;
		}
		System.out.println ("Numero Total de estados= " + alEstadoProb.size());
	}
	
	public ArrayList <Boolean> SortearEstado(ArrayList<ProbSet> alSetProb) {
		// System.out.println("Estados Seguintes: " + alEstadoProb);
		// alEstadoProb.add(new ProbState(0d, new ArrayList<Boolean>()));
		Random alNumber = new Random();
		double rand = alNumber.nextDouble();
		double inicio = 0.0d;
		HashSet <ArrayList <Boolean>> conjuntoSorteado = null;
		int i;
		
		// Primeira camada: Sorteio do conjunto alcançável.
		for (i = 0; i < alSetProb.size(); i++) {
			if ((inicio <= rand) && (rand < inicio + alSetProb.get(i).getProbability())) {
				conjuntoSorteado = alSetProb.get(i).getStatesIn();
				break;
			} else {
				inicio += alSetProb.get(i).getProbability();
			}
		}
		
		if (conjuntoSorteado == null) {
			conjuntoSorteado = alSetProb.get(i - 1).getStatesIn();
		}
		
		// Segunda camada: Sorteio do estado no conjunto (supondo distribuição equiprovável).
		int numeroEstadoSorteado = alNumber.nextInt(conjuntoSorteado.size());
		Iterator <ArrayList <Boolean>> iteradorEstados = conjuntoSorteado.iterator();
		int contador = 0;
		ArrayList <Boolean> estadoSorteado = null;
		while (iteradorEstados.hasNext()) {
			estadoSorteado = iteradorEstados.next();
			if (contador == numeroEstadoSorteado) {
				break;
			} else {
				contador++;
			}
		}
		
		return estadoSorteado;
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
