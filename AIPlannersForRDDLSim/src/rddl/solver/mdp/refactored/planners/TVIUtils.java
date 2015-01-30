package rddl.solver.mdp.refactored.planners;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Stack;

import javax.naming.TimeLimitExceededException;

import rddl.solver.DDUtils;
import rddl.solver.mdp.Action;
import util.ActionTransition;
import util.CString;
import util.MDP;
import util.ProbState;

/**
 * This class has common features used by Topological Value Iteration (TVI)
 * algorithm.
 * 
 * @author felipemartinsss
 *
 */
public class TVIUtils {

	private String _sInstanceName;
	private MDP mdp;
	private LinkedHashMap<Integer, ArrayList<ArrayList<Boolean>>> statesByTopologicalOrder;
	private HashMap<ArrayList<Boolean>, Double> valueFunction;
	private HashMap<ArrayList<Boolean>, Double> previousValueFunction;
	private double maximumBellmanError = 0.001d; // 10^(-3)
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;

	private HashMap<ArrayList<Boolean>, Boolean> discoveredStates = new HashMap<ArrayList<Boolean>, Boolean>();
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private HashMap<Integer, ArrayList<ArrayList<Boolean>>> SCCIdToMetaStates = new HashMap<Integer, ArrayList<ArrayList<Boolean>>>();
	private int tamanhoDaPilha = 0;
	private HashMap<ArrayList<Boolean>, Integer> stateToSCCId = new HashMap<ArrayList<Boolean>, Integer>();
	private HashMap<Integer, Integer> stronglyConnectedComponentsDDs = new HashMap<Integer, Integer>();
	private int numberOfComponents;

	public TVIUtils(String _sInstanceName, MDP mdp) {
		this._sInstanceName = _sInstanceName;
		this.mdp = mdp;
		valueFunction = new HashMap<ArrayList<Boolean>, Double>();
		previousValueFunction = new HashMap<ArrayList<Boolean>, Double>();
		pi = new HashMap<ArrayList<Boolean>, ActionTransition>();
	}

	/**
	 * TVI Algorithm.
	 * 
	 * @param currentAbstractState
	 * @param bellmanError
	 * @param horizon
	 * @throws TimeLimitExceededException
	 */
	public void doTopologicalValueIteration(
			ArrayList<Boolean> currentAbstractState, double bellmanError,
			int horizon) throws TimeLimitExceededException {
		new ArrayList<ArrayList<Boolean>>();
		currentAbstractState.clone();

		ArrayList<ArrayList<Boolean>> mdpAbstractStates = new ArrayList<ArrayList<Boolean>>();

		for (Integer componentId : stronglyConnectedComponentsDDs.keySet()) {
			// System.out.println("Component ID: " + componentId);
			// System.out.println("ADD ID: " +
			// stronglyConnectedComponentsDDs.get(componentId));
			ArrayList<ArrayList<Boolean>> states = statesByTopologicalOrder
					.get(componentId);
			// System.out.println("States: " + states);
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
					abstractState = updateStateTVI(abstractState);
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
	 * Update state value.
	 * 
	 * @param state
	 * @return
	 */
	public ArrayList<Boolean> updateStateTVI(ArrayList<Boolean> state) {
		ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = mdp.getGreedyActionForTVI(state);
		pi.put(stateClone, acaoOtima);
		previousValueFunction.put(stateClone, valueFunction.get(stateClone));
		valueFunction.put(stateClone, acaoOtima.getQValue());
		return state;
	}

	/**
	 * An iterative Depth-First Search (DFS).
	 * 
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

				for (CString a : mdp.get_hmActionName2Action().keySet()) {
					Action action = mdp.get_hmActionName2Action().get(a);
					ActionTransition acao = new ActionTransition(action,
							new ArrayList<ProbState>());
					if (!mdp.acaoDisponivel(state, action)) {
						ArrayList<Boolean> atribb = (ArrayList<Boolean>) state
								.clone();
						atribb = new ArrayList<Boolean>(atribb.subList(1,
								state.size()));

						double recompensa = mdp.get_context().evaluate(
								action._reward, atribb);

						acao.setReward(recompensa);

						ArrayList<ProbState> transicoes = mdp
								.computeSuccessorsProbEnumForTVI(atribb,
										action._hmVarID2CPT,
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
						acao = mdp.getAcao(state, action);
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
	 * A recursive Depth-First Search (DFS).
	 * 
	 * @param state
	 * @param currentHorizon
	 * @param stackOfStates
	 * @param adjacencyList
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

			for (CString a : mdp.get_hmActionName2Action().keySet()) {
				Action action = mdp.get_hmActionName2Action().get(a);
				ActionTransition acao = new ActionTransition(action,
						new ArrayList<ProbState>());
				if (!mdp.acaoDisponivel(state, action)) {
					ArrayList<Boolean> atribb = (ArrayList<Boolean>) state
							.clone();
					atribb = new ArrayList<Boolean>(atribb.subList(1,
							state.size()));

					double recompensa = mdp.get_context().evaluate(
							action._reward, atribb);

					acao.setReward(recompensa);

					ArrayList<ProbState> transicoes = mdp
							.computeSuccessorsProbEnumForTVI(atribb,
									action._hmVarID2CPT, action._csActionName,
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
					acao = mdp.getAcao(state, action);
				}

				ArrayList<ProbState> transicoes = acao.getTransitions();
				for (int i = 0; i < transicoes.size(); i++) {
					ArrayList<Boolean> nextState = transicoes.get(i).nextRepresentant;
					// ArrayList <Boolean> stateAssignClone =
					// (ArrayList<Boolean>) nextState.clone();
					// stateAssignClone.remove(0);
					// double valorBloco =
					// _context.evaluate(stochasticBisimulation,
					// stateAssignClone);
					// System.out.println("StateBlock: " + valorBloco + " = " +
					// transicoes.get(i)._dProb);

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
	 * Kosaraju Algorithm. Computes the Strongly Connected Components (SCCs) of
	 * an MDP. Returns the number of components found.
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

		// stronglyConnectedComponentsDDs

		// System.out.println("Already computed the reachability list and its transposed version...");
		while (!stackOfStates.isEmpty()) {
			Integer componentDD = mdp.get_context().getConstantNode(0);
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
				componentDD = DDUtils.UpdateValue(mdp.get_context(),
						componentDD, state, numberOfComponents + 1);
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
						componentDD = DDUtils.UpdateValue(mdp.get_context(),
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

	// //////////////////////////////
	// Getters and Setters
	// //////////////////////////////

	public HashMap<ArrayList<Boolean>, ActionTransition> getPi() {
		return pi;
	}

	public void setPi(HashMap<ArrayList<Boolean>, ActionTransition> pi) {
		this.pi = pi;
	}
}
