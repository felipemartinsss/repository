package rddl.solver.mdp.refactored.planners;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Random;
import java.util.Stack;

import javax.naming.TimeLimitExceededException;

import rddl.solver.TimeOutException;
import rddl.solver.mdp.Action;
import util.ActionTransition;
import util.CString;
import util.Cronometro;
import util.GeradorDeArquivo;
import util.MDP;
import util.ProbState;

/**
 * This class has common features used by LRTDP algorithm.
 * 
 * @author felipemartinsss
 *
 */
public class LRTDPUtils {

	private Cronometro lrtdpTime;
	private static int OFFLINE = 0;
	private static int ONLINE = 1;
	private static int PLANEJAMENTO = OFFLINE;
	private static int LRTDP = 1;
	private static int PLANEJADOR = LRTDP;
	private static final String LOG_FILE = "ReachabilityModelReductionConvergence";
	private boolean LOG_CONVERGENCE = false;
	private String OS;
	private ArrayList<Boolean> initialState;
	private HashMap<ArrayList<Boolean>, Boolean> solved;
	private int getActionCounter = 0;
	private double valueFunctionS0;
	private HashMap<ArrayList<Boolean>, Double> valueFunction;

	public HashMap<ArrayList<Boolean>, Boolean> getSolved() {
		return mdp.getSolved();
	}

	public void setSolved(HashMap<ArrayList<Boolean>, Boolean> solved) {
		this.mdp.setSolved(solved);
	}

	// Timing variables
	private long _lStartTime; // For timing purposes
	private int _nTimeLimitSecs;
	private double _dDiscount;
	private MDP mdp = null;
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>();
	private HashMap<ArrayList<Boolean>, ActionTransition> pi = null;
	private static boolean USING_BINARY_SEARCH_IN_SAMPLES = true;
	private Integer stochasticBisimulation = -1;
	private String _sInstanceName;

	public LRTDPUtils(String _sInstanceName, MDP mdp) {
		this._sInstanceName = _sInstanceName;
		this.mdp = mdp;
	}

	/**
	 * LRTDP Algorithm
	 * 
	 * @param currentAbstractState
	 * @param bellmanError
	 * @param horizon
	 * @throws TimeLimitExceededException
	 */
	public void doLRTDP(ArrayList<Boolean> currentAbstractState,
			double bellmanError, int horizon) throws TimeLimitExceededException {
		lrtdpTime = new Cronometro();
		Cronometro sixtyTrialsTime = new Cronometro();
		if (PLANEJAMENTO == OFFLINE) {
			lrtdpTime.setStart();
			sixtyTrialsTime.setStart();
			try {
				new GeradorDeArquivo(new StringBuffer()).writeToLog(
						LOG_CONVERGENCE, LOG_FILE, OS, _sInstanceName);
			} catch (IOException e) {
				e.printStackTrace();
			}
			initialState = (ArrayList<Boolean>) currentAbstractState.clone();
			mdp.getSolved().put(initialState, false);
			while (!mdp.getSolved().get(initialState)) {
				initialState = (ArrayList<Boolean>) currentAbstractState
						.clone();
				lrtdp(initialState, bellmanError, horizon);
			}

			lrtdpTime.setEnd();
			currentAbstractState = updateState(currentAbstractState);
			valueFunctionS0 = mdp.getValueFunction().get(currentAbstractState);
			try {
				new GeradorDeArquivo(new StringBuffer()).writeToLog(
						LOG_CONVERGENCE, LOG_FILE, OS, "Fim");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		// System.out.println("Number of trials: " + numberOfTrials);
		return;
	}

	/**
	 * LRTDP Trials.
	 * 
	 * @param currentAbstractState
	 * @param bellmanError
	 * @param horizon
	 */
	public void lrtdp(ArrayList<Boolean> currentAbstractState,
			double bellmanError, int horizon) {

		Stack<ArrayList<Boolean>> estadosVisitados = new Stack<ArrayList<Boolean>>();
		ArrayList<Boolean> state = (ArrayList<Boolean>) currentAbstractState
				.clone();

		// System.out.println("Performing an lrtdp trial...");
		Date seed = new Date();
		Random rand = new Random(seed.getTime());
		double randomTerminateValue;

		while (!mdp.getSolved().get(state)) {
			estadosVisitados.push(state);
			state = updateState(state);

			if (state.equals(initialState)) {
				double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
				try {
					new GeradorDeArquivo(new StringBuffer()).writeToLog(
							LOG_CONVERGENCE, LOG_FILE, OS, instant + "	"
									+ mdp.getValueFunction().get(state));
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}

			randomTerminateValue = rand.nextDouble();
			if (randomTerminateValue > mdp.get_dDiscount()) {
				break;
			} else {
				state = obtemProximoEstado(state, mdp, 40);
			}
		}

		// System.exit(0);

		while (!estadosVisitados.isEmpty()) {
			state = estadosVisitados.pop();

			if (estadosVisitados.isEmpty()) {
				state = updateState(state);
				double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
				try {
					// writeToLog("LRTDPCheckSolved for Trial: " + trials);
					new GeradorDeArquivo(new StringBuffer()).writeToLog(
							LOG_CONVERGENCE, LOG_FILE, OS, instant + "	"
									+ mdp.getValueFunction().get(state));
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

	/**
	 * Updates a state value.
	 * 
	 * @param state
	 * @return
	 */
	public ArrayList<Boolean> updateState(ArrayList<Boolean> state) {
		ArrayList<Boolean> stateClone = (ArrayList<Boolean>) state.clone();
		ActionTransition acaoOtima = getGreedyAction(state);
		pi.put(stateClone, acaoOtima);
		mdp.getValueFunction().put(stateClone, acaoOtima.getQValue());
		return state;
	}

	/**
	 * Sample next state according to probability distribution.
	 * 
	 * @param estado
	 * @param mdp
	 * @param horizon
	 * @return
	 */
	public ArrayList<Boolean> obtemProximoEstado(ArrayList<Boolean> estado,
			MDP mdp, int horizon) {
		Random rand = new Random((new Date()).getTime());
		ActionTransition acao = null;
		ArrayList<Boolean> e = null;
		double probabilidadeSorteada = 0.0d;
		if (PLANEJADOR == LRTDP) {
			acao = pi.get(estado);
		}

		if (acao != null) {
			ProbState t = null;

			if (USING_BINARY_SEARCH_IN_SAMPLES) {
				ArrayList<ProbState> transicoes = acao.getTransitions();
				int indiceInicio = 0;
				int indiceFim = transicoes.size() - 1;
				int indiceMeio;
				do {
					probabilidadeSorteada = rand.nextDouble();
				} while (probabilidadeSorteada == 0.0d);
				while (indiceInicio <= indiceFim) {
					indiceMeio = (indiceInicio + indiceFim) / 2;
					if (indiceMeio >= 1) {
						if (transicoes.get(indiceMeio)._dProb >= probabilidadeSorteada // +
																						// erroAceitavel
								&& (probabilidadeSorteada > transicoes
										.get(indiceMeio - 1)._dProb)) {
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

		double valorBloco = mdp.getValorBloco(e);
		e = mdp.setRepresentant(valorBloco, e);

		return e;
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

	/**
	 * Verifies if the current state already converged given a bellmanError.
	 * 
	 * @param bellmanError
	 * @param pi
	 * @return
	 */

	public boolean checkSolved(MDP mdp, ArrayList<Boolean> estado,
			double bellmanError) {

		boolean rv = true;

		Stack<ArrayList<Boolean>> open = new Stack<ArrayList<Boolean>>();
		Stack<ArrayList<Boolean>> closed = new Stack<ArrayList<Boolean>>();

		if (!mdp.getSolved().get(estado)) {
			open.push(estado);
		}

		while (!open.isEmpty()) {
			estado = open.pop();

			closed.push(estado);

			ActionTransition at = getGreedyAction(estado);
			double residual = Math.abs(mdp.getValueFunction().get(estado)
					- at.getQValue());
			if (residual > bellmanError) {
				rv = false;
				continue;
			}

			// estado = updateState(estado);

			ArrayList<ProbState> transicoes = at.getTransitions();
			ArrayList<ArrayList<Boolean>> uniao = new ArrayList<ArrayList<Boolean>>();
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
					ArrayList<Boolean> alStateClone = (ArrayList<Boolean>) t.nextRepresentant
							.clone();

					if (!mdp.getSolved().get(alStateClone)
							&& !uniao.contains(alStateClone)) {
						open.push(alStateClone);
						uniao.add(alStateClone);
					}
				}
			}
		}

		if (rv == true) {
			for (ArrayList<Boolean> estadoResolvido : closed) {
				mdp.getSolved().put(estadoResolvido, true);
			}
		} else {
			while (!closed.isEmpty()) {
				estado = closed.pop();
				estado = updateState(estado);
				if (estado.equals(initialState)) {
					double instant = (System.currentTimeMillis() - _lStartTime) / 1000d;
					try {
						new GeradorDeArquivo(new StringBuffer()).writeToLog(
								LOG_CONVERGENCE, LOG_FILE, OS, instant + "	"
										+ mdp.getValueFunction().get(estado));
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

	/**
	 * Verify if an action is ready to be used in a current state.
	 * 
	 * @param currentState
	 * @param a
	 * @return
	 */
	public boolean acaoDisponivel(ArrayList<Boolean> currentState, Action a) {
		boolean aplicavel = false;
		// ArrayList <Acao> acoesDisponiveis = enabledActions.get
		// (currentState);
		ArrayList<ActionTransition> acoesDisponiveis = mdp.getEnabledActions().get(currentState);

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

	public void checkTimeLimit() throws TimeOutException {
		double elapsed_time = (System.currentTimeMillis() - _lStartTime) / 1000d;
		if (elapsed_time > (double) _nTimeLimitSecs)
			throw new TimeOutException("Elapsed time " + elapsed_time
					+ " (s) exceeded time limit of " + _nTimeLimitSecs + " (s)");
	}

	// //////////////////////////
	// Getters and Setters
	// //////////////////////////

	public HashMap<ArrayList<Boolean>, Double> getValueFunction() {
		return valueFunction;
	}

	public void setValueFunction(
			HashMap<ArrayList<Boolean>, Double> valueFunction) {
		this.valueFunction = valueFunction;
	}

	public HashMap<ArrayList<Boolean>, ActionTransition> getPi() {
		return pi;
	}

	public void setPi(HashMap<ArrayList<Boolean>, ActionTransition> pi) {
		this.pi = pi;
	}
}
