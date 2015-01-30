package rddl.solver.mdp.refactored.planners;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import javax.naming.TimeLimitExceededException;

import rddl.solver.mdp.Action;
import util.ActionTransition;
import util.CString;
import util.MDP;
import util.ProbState;

/**
 * This class has common features used by Value Iteration (VI)
 * algorithm.
 * 
 * @author felipemartinsss
 *
 */
public class VIUtils {
	private HashMap<ArrayList<Boolean>, Double> valueFunction;
	private HashMap<ArrayList<Boolean>, Double> previousValueFunction;
	private HashMap<ArrayList<Boolean>, Boolean> solved;
	private static final int BRANCO = 0;
	private static final int CINZA = 1;
	private static final int PRETO = 2;
	private double maximumBellmanError = 0.001d; // 10^(-3)
	private double valueFunctionS0;
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private double _dDiscount;
	private HashMap<ArrayList<Boolean>, ActionTransition> pi;
	private Integer stochasticBisimulation;
	private double heuristicaAdmissivel;
	private String _sInstanceName;
	private MDP mdp;
	
	public VIUtils (String _sInstanceName, MDP mdp) {
		this._sInstanceName = _sInstanceName;
		this.mdp = mdp;
		pi = new HashMap<ArrayList<Boolean>, ActionTransition>();
		valueFunction = mdp.getValueFunction();
		previousValueFunction = new HashMap<ArrayList<Boolean>, Double>();
	}
	
	/**
	 * A Breadth-First Search algorithm that is used to identify all 
	 * the MDP states.
	 * @param state
	 * @param horizon
	 * @return
	 */
	public ArrayList<ArrayList<Boolean>> breadthFirstSearch(
			ArrayList<Boolean> state, int horizon) {
		ArrayList<ArrayList<Boolean>> mdpAbstractStates = new ArrayList<ArrayList<Boolean>>();
		HashMap<ArrayList<Boolean>, Integer> stateColorMap = new HashMap<ArrayList<Boolean>, Integer>();
		mdpAbstractStates.add(state);
		stateColorMap.put(state, BRANCO);
		while (!mdpAbstractStates.isEmpty()) {
			state = mdpAbstractStates.get(0);
			if (stateColorMap.get(state) == BRANCO) {
				stateColorMap.put(state, CINZA);
			}

			for (CString a : mdp.get_hmActionName2Action().keySet()) {
				Action action = mdp.get_hmActionName2Action().get(a);
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));
				ArrayList<ProbState> transicoes = mdp.computeSuccessorsProbEnum(
						atribb, action._hmVarID2CPT, action._csActionName, true);
				for (int i = 0; i < transicoes.size(); i++) {
					ArrayList<Boolean> nextState = transicoes.get(i).nextRepresentant;
					if (stateColorMap.get(nextState) == null) {
						mdpAbstractStates.add(nextState);
						stateColorMap.put(nextState, BRANCO);
					}
				}
			}
			mdpAbstractStates.remove(state);
			stateColorMap.put(state, PRETO);
		}

		for (ArrayList<Boolean> key : stateColorMap.keySet()) {
			mdpAbstractStates.add(key);
		}

		return mdpAbstractStates;
	}

	/**
	 * Value Iteration Algorithm.
	 * @param currentAbstractState
	 * @param bellmanError
	 * @param horizon
	 * @throws TimeLimitExceededException
	 */
	public void doValueIteration(ArrayList<Boolean> currentAbstractState,
			double bellmanError, int horizon) throws TimeLimitExceededException {
		ArrayList<Boolean> initialState = (ArrayList<Boolean>) currentAbstractState
				.clone();
		ArrayList<Boolean> state = (ArrayList<Boolean>) currentAbstractState
				.clone();
		ArrayList<ArrayList<Boolean>> mdpAbstractStates = breadthFirstSearch(
				state, horizon);

		for (ArrayList<Boolean> abstractState : mdpAbstractStates) {
			mdp.getValueFunction().put(abstractState, 0.0d);
		}

		while (true) {
			double currentBellmanError = 0;

			for (ArrayList<Boolean> abstractState : mdpAbstractStates) {
				abstractState = updateStateVI(abstractState);
				double residual = Math.abs(mdp.getValueFunction().get(abstractState)
						- previousValueFunction.get(abstractState));
				currentBellmanError = Math.max(currentBellmanError, residual);
			}

			if (currentBellmanError < maximumBellmanError) {
				break;
			}
		}

		valueFunctionS0 = valueFunction.get(initialState);
	}

	/**
	 * Find valid assignments in an abstract state.
	 * @param currentAssignment
	 * @param validAssignments
	 * @param i
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
	 * Verifies if an action is ready to be applied in the current state.
	 * @param currentState
	 * @param a
	 * @return
	 */
	public boolean acaoDisponivel(ArrayList<Boolean> currentState, Action a) {
		boolean aplicavel = false;
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get
		// (currentState);
		ArrayList<ActionTransition> acoesDisponiveis = mdp.getEnabledActions()
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
	 * Get the ActionTransition for a current pair (s, a).
	 * @param currentState
	 * @param a
	 * @return
	 */
	public ActionTransition getAcao(ArrayList<Boolean> currentState, Action a) {
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get
		// (currentState);
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
	 * Update a state value.
	 * @param state
	 * @return
	 */
	public ArrayList<Boolean> updateStateVI(ArrayList<Boolean> state) {
		ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = getGreedyAction(state);
		pi.put(stateClone, acaoOtima);
		previousValueFunction.put(stateClone, mdp.getValueFunction().get(stateClone));
		mdp.getValueFunction().put(stateClone, acaoOtima.getQValue());
		return state;
	}
	
	/**
	 * Gets the greedy action for the current state.
	 * @param state
	 * @return
	 */
	public ActionTransition getGreedyAction(ArrayList<Boolean> state) {
		double gamma = mdp.get_dDiscount();

		ActionTransition acaoOtima = null;
		double qOtimo = -Float.MAX_VALUE;
		Double q = -Double.MAX_VALUE;

		// find best action
		for (CString a : mdp.get_hmActionName2Action().keySet()) {
			Action action = mdp.get_hmActionName2Action().get(a);
			ActionTransition acao = new ActionTransition(action,
					new ArrayList<ProbState>());
			if (!acaoDisponivel(state, action)) {
				ArrayList<Boolean> atribb = (ArrayList<Boolean>) state.clone();
				atribb = new ArrayList<Boolean>(atribb.subList(1, state.size()));

				double recompensa = mdp.get_context().evaluate(action._reward, atribb);
				// _context.getGraph(action._reward).launchViewer();

				acao.setReward(recompensa);

				ArrayList<ProbState> transicoes = mdp.computeSuccessorsProbEnum(
						atribb, action._hmVarID2CPT, action._csActionName, true);
				acao.setTransitions(transicoes);
				ArrayList<ActionTransition> acoesDisponiveis = mdp.getEnabledActions()
						.get(state);
				if (acoesDisponiveis == null) {
					acoesDisponiveis = new ArrayList<ActionTransition>();
				}
				acoesDisponiveis.add(acao);
				mdp.getEnabledActions().put(state, acoesDisponiveis);
			} else {
				acao = mdp.getAcao(state, action);
			}

			ArrayList<ProbState> transicoes = acao.getTransitions();
			double somatorio = 0.0d;

			for (int j = 0; j < transicoes.size(); j++) {
				if (j == 0) {
					ProbState transicao = transicoes.get(j);
					double probabilidade = transicao._dProb;
					double valor = mdp.getValueFunction().get(transicao.nextRepresentant);
					somatorio += probabilidade * valor;
				} else {
					ProbState transicao = transicoes.get(j);
					double probabilidade = (transicao._dProb - transicoes
							.get(j - 1)._dProb);
					double valor = mdp.getValueFunction().get(transicao.nextRepresentant);
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

	////////////////////////////////
	// Getters and setters.
	////////////////////////////////
	
	public HashMap<ArrayList<Boolean>, ActionTransition> getPi() {
		return pi;
	}

	public void setPi(HashMap<ArrayList<Boolean>, ActionTransition> pi) {
		this.pi = pi;
	}
	
	

}
