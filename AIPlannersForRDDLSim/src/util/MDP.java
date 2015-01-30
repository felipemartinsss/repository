package util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Random;
import util.ActionTransition;
import rddl.solver.mdp.Action;
import util.ProbState;
import rddl.translate.RDDL2Format;
import dd.discrete.ADD;
import dd.discrete.ADDDNode;
import dd.discrete.ADDINode;
import dd.discrete.ADDNode;

/**
 * Class that wraps a Markov Decision Process (MDP).
 * 
 * @author felipemartinsss
 */
public class MDP {
	private LinkedHashSet<Estado> estados;
	private LinkedHashSet<Estado> estadosIniciais;
	private LinkedHashSet<Estado> estadosMeta;
	private LinkedHashSet<Acao> acoes;
	HashMap<ArrayList<Boolean>, String> assignToStateName;
	HashMap<ArrayList<Boolean>, ArrayList<Boolean>> assignToRepresentant;
	private float fatorDeDesconto;
	private int iteracoes;
	private int maximoIteracoes;
	private boolean limiteDeIteracoes = false;
	private float erroMaximoPermitido;
	private String algoritmo;
	private HashMap<Double, ArrayList<Boolean>> blockToRepresentant;
	private double heuristicaAdmissivel;
	private ADD _context;
	private ArrayList<Integer> _allMDPADDs;
	private ArrayList<CString> _alStateVars;
	private ArrayList<CString> _alPrimeStateVars;
	private ArrayList<CString> _alActionNames;
	private HashMap<CString, Action> _hmActionName2Action; // Holds transition
	private String _sInstanceName;
	private RDDL2Format _translation = null;
	private Integer stochasticBisimulation = -1;
	private static boolean USING_BINARY_SEARCH_SORTITION = true;
	private HashMap<Integer, Integer> _hmPrimeVarID2VarID;
	private double valueFunctionS0;
	private HashMap<ArrayList<Boolean>, Double> valueFunction;
	private HashMap<ArrayList<Boolean>, Boolean> solved;
	private HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions;
	public HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> getEnabledActions() {
		if (enabledActions == null) {
			enabledActions = new HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>>(); 
		}
		return enabledActions;
	}

	public void setEnabledActions(
			HashMap<ArrayList<Boolean>, ArrayList<ActionTransition>> enabledActions) {
		this.enabledActions = enabledActions;
	}

	private double _dDiscount;
	private int encontreAtribuicaoCalls = 0;
	
	public ADD get_context() {
		return _context;
	}

	public void set_context(ADD _context) {
		this._context = _context;
	}

	/**
	 * Default constructor
	 */
	public MDP() {
		estados = new LinkedHashSet<Estado>();
		estadosIniciais = new LinkedHashSet<Estado>();
		estadosMeta = new LinkedHashSet<Estado>();
		acoes = new LinkedHashSet<Acao>();
		assignToStateName = new HashMap<ArrayList<Boolean>, String>();
		assignToRepresentant = new HashMap<ArrayList<Boolean>, ArrayList<Boolean>>();
		blockToRepresentant = new HashMap<Double, ArrayList<Boolean>>();
		valueFunction = new HashMap<ArrayList<Boolean>, Double>();
		solved = new HashMap<ArrayList<Boolean>, Boolean>();
	}

	/**
	 * Adds a state passed as parameter to the MDP set of states S.
	 * 
	 * @param estado
	 * @return
	 */
	public boolean adicioneEstado(Estado estado) {
		boolean resultado = estados.add(estado);
		return resultado;
	}

	/**
	 * Adds the state passed as parameter to the set of initial states of an MDP (SSP).
	 * 
	 * @param estado
	 * @return
	 */
	public boolean adicioneEstadoInicial(Estado estado) {
		if (estado != null) {
			boolean resultado = estadosIniciais.add(estado);
			return resultado;
		} else {
			return false;
		}
	}

	/**
	 * Sample an initial state inside the set of initial states and returns it to the caller method.
	 * 
	 * @return
	 */
	public Estado obtemEstadoInicial() {
		Random r = new Random();
		int i = 0;
		Estado e = null;
		if (estadosIniciais.size() == 1) {
			e = estadosIniciais.iterator().next();
		} else if (estadosIniciais.size() > 1) {
			i = r.nextInt(estadosIniciais.size());
			Iterator<Estado> iterador = estadosIniciais.iterator();
			int contador = 0;

			while (iterador.hasNext()) {
				e = iterador.next();
				if (i == contador) {
					return e;
				}
				contador++;
			}
		} else {
			i = r.nextInt(estados.size());
			Iterator<Estado> iterador = estados.iterator();
			int contador = 0;

			while (iterador.hasNext()) {
				e = iterador.next();
				if (i == contador) {
					return e;
				}
				contador++;
			}
		}

		return e;
	}

	/**
	 * Adds the state passed as parameter to the set of meta states (SSP).
	 * @param estado
	 * @return
	 */
	public boolean adicioneEstadoMeta(Estado estado) {
		boolean resultado = estadosMeta.add(estado);
		return resultado;
	}

	/**
	 * Converts the current MDP to String representation.
	 * 
	 */
	public String toString() {
		StringBuffer sb = new StringBuffer("");
		Estado e = null;
		ArrayList<Acao> acoesDisponiveis = null;
		Iterator<Estado> eIterator = estados.iterator();
		while (eIterator.hasNext()) {
			e = eIterator.next();
			sb.append("Estado: " + e.getNome() + "\n");
			acoesDisponiveis = e.getAcoesDisponiveis();
			sb.append("Acoes em " + e.getNome()
					+ " (Recompensa) e Transicoes \n");
			for (int i = 0; i < acoesDisponiveis.size(); i++) {
				Acao a = acoesDisponiveis.get(i);
				sb.append("Acao: " + a.getNome() + " (Recompensa: "
						+ a.getRecompensa() + ")\n");
				ArrayList<Transicao> transicoes = a.getTransicoes();
				sb.append(transicoes.size() + " transicoes.\n");
				float soma = 0.0f;
				for (int j = 0; j < transicoes.size(); j++) {
					Transicao t = transicoes.get(j);
					String origem = t.getOrigem();
					String destino = t.getDestino();
					float prob = t.getProbabilidade();
					sb.append("\t P(" + destino + "|" + origem + ","
							+ a.getNome() + ") = " + prob + "\n");
					soma += prob;
				}
				sb.append("P(Destino|" + e.getNome() + "," + a.getNome()
						+ ") = " + soma + "\n");
			}
		}

		sb.append("Fator de Desconto: " + getFatorDeDesconto() + "\n");
		sb.append("Maximo de Iteracoes: " + getMaximoIteracoes() + "\n");
		sb.append("Erro maximo permitido: " + getErroMaximoPermitido() + "\n");
		sb.append("Numero de estados: " + getNumeroEstados() + "\n");

		return sb.toString();

	}

	/**
	 * Adds an action to the set of Actions of this MDP.
	 * 
	 * @param acao
	 * @return
	 */
	public boolean adicioneAcao(Acao acao) {
		boolean resultado = acoes.add(acao);
		return resultado;
	}

	/**
	 * Receives a partial policy for the current MDP and computes the maximum error
	 * of reachable states using that policy and initial state.
	 * 
	 * @param pi
	 * @return
	 */
	public float erroMaximoRTDP(Estado estadoInicial, Politica pi) {
		LinkedHashSet<Estado> estados = new LinkedHashSet<Estado>();
		estados.addAll(pi.getEstados());
		estados.add(estadoInicial);
		LinkedHashSet<Estado> estadosAlcancaveis = new LinkedHashSet<Estado>();
		for (Estado e : estados) {
			Acao politicaAtualE = pi.getAcao(e);
			if (politicaAtualE != null) {
				ArrayList<Transicao> transicoes = politicaAtualE
						.getTransicoes();
				for (Transicao t : transicoes) {
					Estado estadoAlcancavel = getEstado(t.getDestino());
					if (t.getProbabilidade() > 0) {
						estadosAlcancaveis.add(estadoAlcancavel);
					}
				}
			}
		}

		// System.out.println("Estados alcancaveis pela politica atual: " +
		// estadosAlcancaveis);
		// System.out.println("Quantidade de estados alcancaveis pela politica atual: "
		// + estadosAlcancaveis.size());

		float erroAtual;
		if (estadosAlcancaveis.size() > 0) {
			float erroMaximo = 0.0f;
			for (Estado e : estadosAlcancaveis) {
				ArrayList<Float> funcaoValorE = e.getFuncaoValor();
				int ultimaAtualizacao = funcaoValorE.size() - 1;

				if (ultimaAtualizacao > 0) {
					erroAtual = Math.abs(e.getUltimoValor()
							- funcaoValorE.get(ultimaAtualizacao - 1));
					if (erroMaximo <= erroAtual) {
						erroMaximo = erroAtual;
					}
				} else {
					erroMaximo = Float.MAX_VALUE;
				}
			}
			return erroMaximo;
		} else {
			// Nenhum estado alcancavel pela politica atual.
			return Float.MAX_VALUE;
		}

	}

	/**
	 * Gets the maximum error between the last and pre-last value function computed.
	 * @return
	 */
	public float erroMaximo() {
		Iterator<Estado> iterator = estados.iterator();
		Float erroMaximo = 0.0f;
		Estado e = null;
		String nomeEstado = null;

		if (iterator.hasNext()) {
			e = iterator.next();
			nomeEstado = e.getNome();
			erroMaximo = e.residual(algoritmo);
			while (iterator.hasNext()) {
				e = iterator.next();
				if (erroMaximo < e.residual(algoritmo)) {
					erroMaximo = e.residual(algoritmo);
					nomeEstado = e.getNome();
				}
			}
		}
		return erroMaximo;
	}

	/**
	 * Gets the set of meta states of current MDP. Useful for implementations of 
	 * RTDP, LRTDP, BRTDP, etc.
	 * @return
	 */
	public LinkedHashSet<Estado> getEstadosMeta() {
		if (estadosMeta == null) {
			boolean sIsMeta;
			estadosMeta = new LinkedHashSet<Estado>();
			Iterator<Estado> eIterator = estados.iterator();
			while (eIterator.hasNext()) {
				Estado s = eIterator.next();
				sIsMeta = true;
				ArrayList<Acao> acoesDisponiveis = s.getAcoesDisponiveis();

				if (acoesDisponiveis.size() == 0) {
					sIsMeta = false;
				} else {
					for (int i = 0; i < acoesDisponiveis.size(); i++) {
						Acao a = acoesDisponiveis.get(i);
						ArrayList<Transicao> transicoes = a.getTransicoes();
						if (transicoes.size() != 1 || a.getRecompensa() != 0) {
							sIsMeta = false;
							break;
						}
					}
				}
				if (sIsMeta) {
					estadosMeta.add(s);
				}
			}
		}

		return estadosMeta;
	}

	/**
	 * Prints the last values of Value Function.
	 */
	public void imprimeFuncaoValor() {
		LinkedHashSet<Estado> estados = getEstados();
		Iterator<Estado> iterator = estados.iterator();
		while (iterator.hasNext()) {
			Estado s = iterator.next();
			System.out.print("V(" + s.getNome() + ") = (" + s.getUltimoValor()
					+ "), ");
		}
		System.out.println();
	}

	/**
	 * For all pair of (state, action), find the min reward and returns this value.
	 * 
	 * @return
	 */
	public float getRecompensaMinima() {
		Iterator<Estado> iterator = estados.iterator();
		float recompensaMinima = Float.MAX_VALUE;
		if (iterator.hasNext()) {
			Estado e = iterator.next();
			ArrayList<Acao> acoes = e.getAcoesDisponiveis();
			Iterator<Acao> iteradorAcoes = acoes.iterator();
			if (iteradorAcoes.hasNext()) {
				Acao a = iteradorAcoes.next();
				recompensaMinima = a.getRecompensa();
				while (iteradorAcoes.hasNext()) {
					a = iteradorAcoes.next();
					if (a.getRecompensa() < recompensaMinima) {
						recompensaMinima = a.getRecompensa();
					}
				}
			}

			while (iterator.hasNext()) {
				e = iterator.next();
				acoes = e.getAcoesDisponiveis();
				iteradorAcoes = acoes.iterator();
				while (iteradorAcoes.hasNext()) {
					Acao a = iteradorAcoes.next();
					if (a.getRecompensa() < recompensaMinima) {
						recompensaMinima = a.getRecompensa();
					}
				}
			}
		}
		return recompensaMinima;
	}

	/**
	 * 
	 * For all pairs (state, action), finds the pair of max reward and returns this value.
	 * 
	 * @return
	 */
	public float getRecompensaMaxima() {
		Iterator<Estado> iterator = estados.iterator();
		float recompensaMaxima = Float.MIN_VALUE;
		if (iterator.hasNext()) {
			Estado e = iterator.next();
			ArrayList<Acao> acoes = e.getAcoesDisponiveis();
			Iterator<Acao> iteradorAcoes = acoes.iterator();
			if (iteradorAcoes.hasNext()) {
				Acao a = iteradorAcoes.next();
				recompensaMaxima = a.getRecompensa();
				while (iteradorAcoes.hasNext()) {
					a = iteradorAcoes.next();
					if (a.getRecompensa() > recompensaMaxima) {
						recompensaMaxima = a.getRecompensa();
					}
				}
			}

			while (iterator.hasNext()) {
				e = iterator.next();
				acoes = e.getAcoesDisponiveis();
				iteradorAcoes = acoes.iterator();
				while (iteradorAcoes.hasNext()) {
					Acao a = iteradorAcoes.next();
					if (a.getRecompensa() > recompensaMaxima) {
						recompensaMaxima = a.getRecompensa();
					}
				}
			}
		}
		return recompensaMaxima;
	}

	/**
	 * Normalizes reward function putting its value between [0,1].
	 */
	public void normalizaRecompensa() {
		float recompensaMin = getRecompensaMinima();
		float recompensaMax = getRecompensaMaxima();
		System.out.println("Recompensa dom�nio: [" + recompensaMin + ", "
				+ recompensaMax + "]");
		float intervaloRecompensa = recompensaMax - recompensaMin;
		if (recompensaMax - recompensaMin > 1) {
			Iterator<Estado> iteradorEstados = estados.iterator();
			while (iteradorEstados.hasNext()) {
				Estado e = iteradorEstados.next();
				ArrayList<Acao> acoes = e.getAcoesDisponiveis();
				Iterator<Acao> iteradorAcoes = acoes.iterator();
				while (iteradorAcoes.hasNext()) {
					Acao a = iteradorAcoes.next();
					if (intervaloRecompensa != 0) {
						float novoValorRecompensa = (a.getRecompensa() - recompensaMin)
								/ intervaloRecompensa;
						// System.out.println("Novos valores: " +
						// novoValorRecompensa);
						a.setRecompensa(novoValorRecompensa);
					}
				}
			}
		}
	}

	/**
	 * Finds a state that satisfies a assignment.
	 * @param atribuicaoX
	 * @return
	 */
	public Estado encontreEstadoAtribuicao(ArrayList<Boolean> atribuicaoX) {
		setEncontreAtribuicaoCalls(getEncontreAtribuicaoCalls() + 1);
		/*
		 * for (Estado s : estados) { if (s != null) { HashSet <ArrayList
		 * <Boolean>> atribuicoes = s.getAtribuicoes(); if
		 * (atribuicoes.contains(atribuicaoX)) { return s; } } }
		 * 
		 * return null;
		 */

		boolean atribuicaoIgual;
		// System.out.print(atribuicaoX + " = ");
		if (atribuicaoX != null) {
			for (Estado s : estados) {
				if (s != null) {
					HashSet<ArrayList<Boolean>> atribuicoes = s
							.getAtribuicoes();
					if (atribuicoes != null) {
						Iterator<ArrayList<Boolean>> iteradorAtribuicoes = atribuicoes
								.iterator();
						while (iteradorAtribuicoes.hasNext()) {
							ArrayList<Boolean> atribuicao = iteradorAtribuicoes
									.next();
							// System.out.println("Atribuicao comparada = " +
							// atribuicao);
							atribuicaoIgual = true;
							for (int i = 0; i < atribuicao.size(); i++) {
								if ((atribuicao.get(i) != null)
										&& (atribuicaoX.get(i) != null)) {
									if (atribuicao.get(i).booleanValue() != atribuicaoX
											.get(i).booleanValue()) {
										atribuicaoIgual = false;
										break;
									}
								}
							}

							if (atribuicaoIgual) {
								// System.out.println(atribuicao);
								return s;
							}
						}
					}
				}
			}
		}
		return null;
	}

	/**
	 * Find a state that satisfied a assignment.
	 * @param atribuicaoX
	 * @return
	 */
	public Estado optimizedEncontreEstadoAtribuicao(
			ArrayList<Boolean> atribuicaoX) {
		// System.out.print(atribuicaoX + " = ");

		if (atribuicaoX != null) {

			String nomeEstado = assignToStateName.get(atribuicaoX);

			if (nomeEstado != null) {
				Estado s = this.getEstado(nomeEstado);
				if (s != null) {
					return s;
				}
			}
		}
		return null;

	}

	/**
	 * Print assignments in the current state if it is abstract.
	 */
	public void imprimeAtribuicoes() {
		for (Estado s : estados) {
			HashSet<ArrayList<Boolean>> atribuicoesEmS = s.getAtribuicoes();
			if (atribuicoesEmS != null) {
				System.out.println("Atribuicoes em " + s.getNome());
				Iterator<ArrayList<Boolean>> iteradorAtribuicoesEmS = atribuicoesEmS
						.iterator();
				while (iteradorAtribuicoesEmS.hasNext()) {
					ArrayList<Boolean> atribuicao = iteradorAtribuicoesEmS
							.next();
					System.out.println(atribuicao);
				}
			}
		}
	}

	/**
	 * Remove a state from the set of initial states.
	 */
	public void removeEstadoInicial() {
		if (estadosIniciais.size() != 0) {
			estadosIniciais.remove(0);
		}
	}

	
	/**
	 * Add assignment to a state.
	 * @param assign
	 * @param stateName
	 * @return
	 */
	public boolean addAssignToStateNamePair(ArrayList<Boolean> assign,
			String stateName) {
		if (assignToStateName != null) {
			assignToStateName.put(assign, stateName);
			String stringInserted = assignToStateName.get(assign);
		}
		return false;
	}

	/**
	 * Add a representant to an abstract state.
	 * @param assignment
	 * @param currentAbstractState
	 */
	public void addRepresentantToCurrentState(ArrayList<Boolean> assignment,
			ArrayList<Boolean> currentAbstractState) {
		if (assignToRepresentant == null) {
			assignToRepresentant = new HashMap<ArrayList<Boolean>, ArrayList<Boolean>>();
		}
		assignToRepresentant.put(currentAbstractState, currentAbstractState);

	}
	

	/**
	 * Modify to stop using ArrayList <ProbState>
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

		if (USING_BINARY_SEARCH_SORTITION) {
			for (int i = 1; i < transicoes.size(); i++) {
				double probabilidadeI = transicoes.get(i)._dProb;
				double probabilidadeIAnterior = transicoes.get(i - 1)._dProb;
				transicoes.get(i)._dProb = probabilidadeI
						+ probabilidadeIAnterior;
			}
		}

		transicoes.get(transicoes.size() - 1)._dProb = 1.0d;

		// System.out.println("Transicao = " + transicoes.get(transicoes.size()
		// - 1)._dProb);

		return transicoes;
	}
	
	/**
	 * Find the next states according to the CPTs.
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

					// Estado sAux =
					// mdp.optimizedEncontreEstadoAtribuicao(newAssign);
					// ArrayList <Boolean> representantAux =
					// mdp.getRepresentant(newAssign);
					ArrayList<Boolean> representantAux = getRepresentant(valorBloco);

					if (representantAux != null) {
						// Transi��o para um estado que j� foi adicionado ao
						// MDP.
						boolean transitionExists = false;
						for (int i = 0; i < transicoes.size(); i++) {
							ProbState t = transicoes.get(i);
							double valorBlocoAlState = getValorBloco(t.nextRepresentant);
							ArrayList<Boolean> alStateRepresentant = setRepresentant(
									valorBlocoAlState, t.nextRepresentant);

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
								ArrayList<Boolean> representant = setRepresentant(
										valorBloco, stateAssignClone);
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

									ArrayList<Boolean> representant = setRepresentant(
											valorBloco, assignment);
									boolean transitionExists = false;
									for (int i = 0; i < transicoes.size(); i++) {
										t = transicoes.get(i);
										double valorBlocoAlState = getValorBloco(t.nextRepresentant);
										ArrayList<Boolean> alStateRepresentant = setRepresentant(
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
	 * Get current value of a block of states.
	 * @param assign
	 * @return
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

	/**
	 * Method to find valid assignments in an abstract state.s
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
	 * Get GreedyAction used by TVI algorithm.
	 * @param state
	 * @return
	 */
	public ActionTransition getGreedyActionForTVI(ArrayList<Boolean> state) {
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

				ArrayList<ProbState> transicoes = computeSuccessorsProbEnumForTVI(
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
	 * Gets the greedy action for the current state.
	 * @param state
	 * @return
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
				if (j == 0) {
					ProbState transicao = transicoes.get(j);
					double probabilidade = transicao._dProb;
					double valor = valueFunction
							.get(transicao.nextRepresentant);
					somatorio += probabilidade * valor;
				} else {
					ProbState transicao = transicoes.get(j);
					double probabilidade = (transicao._dProb - transicoes
							.get(j - 1)._dProb);
					double valor = valueFunction
							.get(transicao.nextRepresentant);
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
	 * Gets an ActionTransition to compute state value.
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
	 * Verifies if an action is ready to be used in currentState.
	 * @param currentState
	 * @param a
	 * @return
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
	 * Modify to stop using ArrayList <ProbState>
	 * 
	 * @param state
	 * @param iD2ADD
	 * @param _csActionName
	 * @return
	 */
	public ArrayList<ProbState> computeSuccessorsProbEnumForTVI(
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

		/*
		 * if (USING_BINARY_SEARCH_SORTITION) { for (int i = 1; i <
		 * transicoes.size(); i++) { double probabilidadeI =
		 * transicoes.get(i)._dProb; double probabilidadeIAnterior =
		 * transicoes.get(i - 1)._dProb; transicoes.get(i)._dProb =
		 * probabilidadeI + probabilidadeIAnterior; } }
		 * transicoes.get(transicoes.size() - 1)._dProb = 1.0d;
		 */

		// System.out.println("Transicao = " + transicoes.get(transicoes.size()
		// - 1)._dProb);

		return transicoes;
	}

	// ////////////////////////////////////////
	// Getters and setters.
	// ////////////////////////////////////////
	
	public HashMap<ArrayList<Boolean>, Double> getValueFunction() {
		return valueFunction;
	}

	public void setValueFunction(
			HashMap<ArrayList<Boolean>, Double> valueFunction) {
		this.valueFunction = valueFunction;
	}
	
	public float getErroMaximoPermitido() {
		return erroMaximoPermitido;
	}

	public void setErroMaximoPermitido(float erroMaximoPermitido) {
		this.erroMaximoPermitido = erroMaximoPermitido;
	}

	public ArrayList<Integer> get_allMDPADDs() {
		return _allMDPADDs;
	}

	public void set_allMDPADDs(ArrayList<Integer> _allMDPADDs) {
		this._allMDPADDs = _allMDPADDs;
	}

	public ArrayList<CString> get_alStateVars() {
		return _alStateVars;
	}

	public void set_alStateVars(ArrayList<CString> _alStateVars) {
		this._alStateVars = _alStateVars;
	}

	public ArrayList<CString> get_alPrimeStateVars() {
		return _alPrimeStateVars;
	}

	public void set_alPrimeStateVars(ArrayList<CString> _alPrimeStateVars) {
		this._alPrimeStateVars = _alPrimeStateVars;
	}

	public ArrayList<CString> get_alActionNames() {
		return _alActionNames;
	}

	public void set_alActionNames(ArrayList<CString> _alActionNames) {
		this._alActionNames = _alActionNames;
	}

	public HashMap<CString, Action> get_hmActionName2Action() {
		return _hmActionName2Action;
	}

	public void set_hmActionName2Action(
			HashMap<CString, Action> _hmActionName2Action) {
		this._hmActionName2Action = _hmActionName2Action;
	}

	public RDDL2Format get_translation() {
		return _translation;
	}

	public void set_translation(RDDL2Format _translation) {
		this._translation = _translation;
	}

	public Integer getStochasticBisimulation() {
		return stochasticBisimulation;
	}

	public void setStochasticBisimulation(Integer stochasticBisimulation) {
		this.stochasticBisimulation = stochasticBisimulation;
	}

	public static boolean isUSING_BINARY_SEARCH_SORTITION() {
		return USING_BINARY_SEARCH_SORTITION;
	}

	public static void setUSING_BINARY_SEARCH_SORTITION(
			boolean uSING_BINARY_SEARCH_SORTITION) {
		USING_BINARY_SEARCH_SORTITION = uSING_BINARY_SEARCH_SORTITION;
	}

	public HashMap<Integer, Integer> get_hmPrimeVarID2VarID() {
		return _hmPrimeVarID2VarID;
	}

	public void set_hmPrimeVarID2VarID(
			HashMap<Integer, Integer> _hmPrimeVarID2VarID) {
		this._hmPrimeVarID2VarID = _hmPrimeVarID2VarID;
	}

	public HashMap<ArrayList<Boolean>, Boolean> getSolved() {
 		return solved;
	}

	public void setSolved(HashMap<ArrayList<Boolean>, Boolean> solved) {
		this.solved = solved;
	}

	public double get_dDiscount() {
		return _dDiscount;
	}

	public void set_dDiscount(double _dDiscount) {
		this._dDiscount = _dDiscount;
	}

	public String get_sInstanceName() {
		return _sInstanceName;
	}

	public void set_sInstanceName(String _sInstanceName) {
		this._sInstanceName = _sInstanceName;
	}

	public double getHeuristicaAdmissivel() {
		return heuristicaAdmissivel;
	}

	public void setHeuristicaAdmissivel(double heuristicaAdmissivel) {
		this.heuristicaAdmissivel = heuristicaAdmissivel;
	}
	
	/**
	 * Obt�m o conjunto de estados do MDP atual.
	 * 
	 * @return the estados
	 */
	public LinkedHashSet<Estado> getEstados() {
		return estados;
	}

	/**
	 * Atualiza o conjunto de estados do MDP atual.
	 * 
	 * @param estados
	 *            the estados to set
	 */
	public void setEstados(LinkedHashSet<Estado> estados) {
		this.estados = estados;
	}

	/**
	 * Obt�m o conjunto de a��es do MDP atual.
	 * 
	 * @return the acoes
	 */
	public LinkedHashSet<Acao> getAcoes() {
		return acoes;
	}

	/**
	 * Atualiza o conjunto de a��es do MDP atual.
	 * 
	 * @param acoes
	 *            the acoes to set
	 */
	public void setAcoes(LinkedHashSet<Acao> acoes) {
		this.acoes = acoes;
	}

	/**
	 * Obt�m o fator de desconto.
	 * 
	 * @return the fatorDeDesconto
	 */
	public float getFatorDeDesconto() {
		return fatorDeDesconto;
	}

	/**
	 * Ajusta o fator de desconto.
	 * 
	 * @param fatorDeDesconto
	 *            the fatorDeDesconto to set
	 */
	public void setFatorDeDesconto(float fatorDeDesconto) {
		this.fatorDeDesconto = fatorDeDesconto;
	}

	public int getNumeroEstados() {
		return estados.size();
	}

	public Estado getEstado(String nome) {
		Iterator<Estado> iterator = estados.iterator();
		while (iterator.hasNext()) {
			Estado e = iterator.next();
			if ((e != null) && (e.getNome().equals(nome))) {
				return e;
			}
		}
		return null;
	}

	public Acao getAcao(String nome) {
		Iterator<Acao> iterator = acoes.iterator();
		while (iterator.hasNext()) {
			Acao a = iterator.next();
			if ((a != null) && (a.getNome().equals(nome))) {
				return a;
			}
		}
		return null;
	}

	public int getMaximoIteracoes() {
		return maximoIteracoes;
	}

	public void setMaximoIteracoes(int maximoIteracoes) {
		this.maximoIteracoes = maximoIteracoes;
		setLimiteDeIteracoes(true);
	}
	
	public String getAlgoritmo() {
		return algoritmo;
	}
	
	public void setAlgoritmo(int opcao) {
		if (opcao == 1) {
			algoritmo = "IV";
		} else if (opcao == 2) {
			algoritmo = "RTDP";
		} else if (opcao == 3) {
			algoritmo = "LRTDP";
		}
	}

	public void setIteracoes(int iteracoes) {
		this.iteracoes = iteracoes;
	}

	public int getIteracoes() {
		return iteracoes;
	}


	public boolean isLimiteDeIteracoes() {
		return limiteDeIteracoes;
	}

	public void setLimiteDeIteracoes(boolean limiteDeIteracoes) {
		this.limiteDeIteracoes = limiteDeIteracoes;
	}
	
	public int getEncontreAtribuicaoCalls() {
		return encontreAtribuicaoCalls;
	}

	public void setEncontreAtribuicaoCalls(int encontreAtribuicaoCalls) {
		this.encontreAtribuicaoCalls = encontreAtribuicaoCalls;
	}

	public ArrayList<Boolean> getRepresentant(
			ArrayList<Boolean> atribuicaoClonada) {
		if (assignToRepresentant != null) {
			return assignToRepresentant.get(atribuicaoClonada);
		} else {
			return null;
		}
	}

	public ArrayList<Boolean> getRepresentant(Double blockValue) {
		if (blockToRepresentant != null) {
			ArrayList<Boolean> blockRepresentant = blockToRepresentant
					.get(blockValue);
			return blockRepresentant;
		}
		return null;
	}

	public ArrayList<Boolean> setRepresentant(Double blockValue,
			ArrayList<Boolean> currentState) {
		if (blockToRepresentant != null) {
			if (blockToRepresentant.get(blockValue) == null) {
				blockToRepresentant.put(blockValue, currentState);
				return blockToRepresentant.get(blockValue);
			} else {
				return blockToRepresentant.get(blockValue);
			}
		}
		return null;
	}
	
}
