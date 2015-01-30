package util;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

/**
 * Classe que representa um estado do conjunto de estados do MDP.
 * @author fmsantos
 */
public class Estado implements Comparable <Estado>, Cloneable {
    
    // Nome identificador do estado atual.
    private String nome;
    
    // Define a recompensa de se permanecer no estado atual.
    private float recompensa;
    
    // Define as acoes aplicaveis no estado atual.
    private ArrayList <Acao> acoesDisponiveis;
    
    private ArrayList <Float> funcaoValor;

    private Acao acaoOtima;

    // Utilizada em implementa��es do algoritmo LRTDP.
    private boolean resolvido;
    
    // Utilizada em implementa��es de agrega��o.
    private boolean agregado;
    
    // Utilizada em implementa��es de agrega��o. Soma do estado atual com rela��o a
    // estado e a��o atual.
    private float soma;
    
    // Define atribui��o de vari�veis de estado que representa o estado atual.
    // Se atribuicoes.size() == 0, h� um �nico estado.
    // Se atribuicoes.size() >= 1, o estado representa um estado abstrato proveniente de v�rios outros estados.
    private HashSet <ArrayList <Boolean>> atribuicoes;
    
    private boolean carregado = false;

	private double b;
	
	private int horizonte;

    /**
     * Verifica se o estado atual pertence ou n�o a algum estado agregado.
     * @return
     */
    public boolean isAgregado() {
		return agregado;
	}

    /**
     * Ajusta agregado para true se o estado atual pertence a algum estado agregado
     * e para false caso contr�rio.
     * @param agregado
     */
	public void setAgregado(boolean agregado) {
		this.agregado = agregado;
	}

	
	private Estado() {
		setHorizonte(0);
	}
	
	/**
	 *	Construtor. Recebe um nome para o estado atual. 
	 * 	@param nome
	 */
    public Estado (String nome) {
        this.nome = nome;
        funcaoValor = new ArrayList <Float> ();
        this.acoesDisponiveis = new ArrayList <Acao>();
        acaoOtima = null;
        atribuicoes = new HashSet<ArrayList<Boolean>>();
        setHorizonte(0);
    }

    /**
     * Obt�m o nome do estado atual.
     * @return
     */
    public String getNome () {
        return nome;
    }

    /**
     * Ajusta o nome do estado atual.
     * @param nome
     */
    public void setNome (String nome) {
        this.nome = nome;
    }
    
    /**
     * Adiciona uma a��o ao conjunto de a��es aplic�veis do estado atual.
     * @param a
     * @return
     */
    public boolean adicionaAcao(Acao a) {
        boolean resultado = false;
        if (a != null) {
            resultado = acoesDisponiveis.add(a);
        }
        return resultado;
    }

    /**
     * Obt�m o n�mero de a��es aplic�veis no estado atual.
     * @return
     */
    public int getNumAcoesDisponiveis() {
        return acoesDisponiveis.size();
    }

    /**
     * Obt�m a recompensa do estado atual quando trabalhamos com R(s) ao inv�s de R(s,a).
     * @return the recompensa
     */
    public float getRecompensa() {
        return recompensa;
    }

    /**
     * Ajusta a recompensa do estado atual quando trabalhamos com R(s).
     * @param recompensa the recompensa to set
     */
    public void setRecompensa(float recompensa) {
        this.recompensa = recompensa;
    }

    /**
     * Obt�m as a��es aplic�veis no estado atual.
     * @return the acoesDisponiveis
     */
    public ArrayList <Acao> getAcoesDisponiveis() {
        return acoesDisponiveis;
    }

    /**
     * Obt�m a i-�sima a��o aplic�vel no estado atual.
     * @param i
     * @return
     */
    public Acao getAcaoDisponivel(int i) {
        return acoesDisponiveis.get(i);
    }

    /**
     * Obt�m true se o estado atual j� convergiu e false caso contr�rio.
     * @return
     */
    public boolean isResolvido() {
        return resolvido;
    }

    /**
     * Define o estado atual como resolvido (valor = true) ou n�o resolvido (valor = false).
     * @param valor
     */
    public void setResolvido (boolean valor) {
        this.resolvido = valor;
    }

    /**
     * Obt�m a fun��o valor no estado atual do est�gio 0 at� o �ltimo est�gio calculado.
     * @return the funcaoValor
     */
    public ArrayList<Float> getFuncaoValor() {
        return funcaoValor;
    }

    /**
     * Ajusta a fun��o valor com uma lista de valores para o estado atual.
     * @param funcaoValor the funcaoValor to set
     */
    public void setFuncaoValor(ArrayList<Float> funcaoValor) {
        this.funcaoValor = funcaoValor;
    }

    /**
     * Insere um novo valor para o �ltimo est�gio calculado da fun��o valor no estado atual.
     * @param novoValor
     */
    public void atualizaFuncaoValor (Float novoValor) {
        funcaoValor.add(novoValor);
        if (funcaoValor.size() >= 3) {
        	funcaoValor.remove(0);
        }
        // if (funcaoValor.size() > 2) {
        //	System.out.println(funcaoValor);
        //	funcaoValor.remove(0);
        //	System.out.println(funcaoValor);
        // }
    }

    /**
     * Obt�m o n�mero de atualiza��es j� realizadas para o estado atual.
     * @return
     */
    public int getNumAtualizacoesFuncaoValor () {
        return funcaoValor.size();
    }

    /**
     * Obt�m o �ltimo valor da fun��o valor calculada para o estado atual.
     * @return
     */
    public float getUltimoValor() {
        int t = funcaoValor.size() - 1;
        if (t >= 0) {
        	return funcaoValor.get(t);
        } else {
        	return 0.0f;
        }
    }

    /**
     * Calcula o residual do estado atual considerando q como �ltimo valor e o �ltimo
     * valor da fun��o como se fosse o pen�ltimo.
     * @param q
     * @return
     */
    public float residual (float q) {
        int estagiosParaFrente = funcaoValor.size() - 1;
        System.out.println("estagios para frente: " + estagiosParaFrente);
        if (estagiosParaFrente >= 0) {
            float residual = Math.abs(q - funcaoValor.get(estagiosParaFrente));
            System.out.println("residual: " + residual);
            return residual;
        } else {
        	System.out.println("returning max value");
            return Float.MAX_VALUE;
        }
    }
    
    public float residual () {
        int tamanhoFuncaoValor = funcaoValor.size();
        if (tamanhoFuncaoValor >= 2) {
            float residual = Math.abs(funcaoValor.get(tamanhoFuncaoValor - 1) - funcaoValor.get(tamanhoFuncaoValor - 2));
            return residual;
        } else {
        	// System.out.println("Estado " + this.getNome() + " ainda n�o foi atualizado vezes o suficiente.");
            return Float.MAX_VALUE;
        }
    }

    /**
     * Calcula o residual de acordo com o algoritmo sendo executado.
     * @param algoritmo
     * @return
     */
    public float residual(String algoritmo) {
        int t = funcaoValor.size() - 1;
        if (t >= 1) {
            float residual = Math.abs(funcaoValor.get(t) - funcaoValor.get(t - 1));
            return residual;
        } else {
            if (algoritmo.equals("RTDP")) {
                return 0.0f;
            }
            return Float.MAX_VALUE;
        }
        
    }

    /**
     * Obt�m a a��o �tima do estado atual.
     * @return the acaoOtima
     */
    public Acao getAcaoOtima() {
        return acaoOtima;
    }

    /**
     * Ajusta a a��o �tima do estado atual.
     * @param acaoOtima the acaoOtima to set
     */
    public void setAcaoOtima(Acao acaoOtima) {
        this.acaoOtima = acaoOtima;
    }

    /**
     * Obt�m uma a��o aplic�vel no estado atual a partir de seu nome.
     * Se a a��o n�o existe, cria a a��o.
     * @param nomeAcao
     * @return
     */
    public Acao getAcao(String nomeAcao) {
        int i;
        int numAcoes = acoesDisponiveis.size();
        for (i = 0; i < numAcoes; i++) {
            Acao a = acoesDisponiveis.get(i);
            if (a.getNome().equals(nomeAcao)) {
                return a;
            }
        }
        Acao a = new Acao(nomeAcao);
        acoesDisponiveis.add(a);
        return a;
    }

    /**
     * Verifica se o estado atual � igual a algum outro estado.
     * Dois estado s�o iguais se t�m o mesmo nome.
     */
    @Override
    public boolean equals (Object outroEstado) {
        if (outroEstado instanceof Estado) {
            Estado e = ((Estado) outroEstado);
            if (this.nome.equals(e.getNome())) {
            	if (this.horizonte == e.getHorizonte()) { // LR2TDP
            		return true;
            	} else {
            		return false;
            	}
            } else {
                return false;
            }
        } else {
            return false;
        }

    }

    /**
     * Obt�m o c�digo hash do estado atual.
     */
    @Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.nome != null ? this.nome.hashCode() : 0) + horizonte * 117;
        return hash;
    }

    /**
     * Obt�m a soma do estado atual.
     * @return
     */
	public float getSoma() {
		return soma;
	}

	/**
	 * Ajusta a soma do estado atual.
	 * @param soma
	 */
	public void setSoma(float soma) {
		this.soma = soma;
	}

	@Override
	public int compareTo(Estado outroEstado) {
		Estado e = (Estado) outroEstado;
		if (this.getUltimoValor() == e.getUltimoValor()) {
			return 0;
		} else if (this.getUltimoValor() > e.getUltimoValor()) {
			return 1;
		} else {
			return -1;
		}
	}
	
	public Acao getAcaoMaxRecompensa () {
		Acao a = null;
		ArrayList <Acao> acoesDisponiveis = getAcoesDisponiveis();
		if (acoesDisponiveis.size() > 0) {
			a = acoesDisponiveis.get(0);
			for (int i = 1; i < acoesDisponiveis.size(); i++) {
				Acao aTemp = acoesDisponiveis.get(i);
				if (a.getRecompensa() < aTemp.getRecompensa()) {
					a = aTemp;
				}
			}
		}
		return a;
	}

	public boolean getAgregado() {
		return agregado;
	}

	/**
	 * Obt�m a atribui��o de vari�veis de estado que representa o estado atual.
	 * @return
	 */
	public HashSet<ArrayList <Boolean>> getAtribuicoes() {
		return atribuicoes;
	}

	/**
	 * Ajusta a atribui��o das vari�veis de estado necess�rias para representa o estado atual.
	 * @param atribuicao
	 */
	public void setAtribuicoes(HashSet<ArrayList <Boolean>> atribuicoes) {
		this.atribuicoes = atribuicoes;
	}
	
	public void adicionaAtribuicao (ArrayList <Boolean> atribuicao) {
		if (atribuicoes != null) {
			atribuicoes.add(atribuicao);
		}
	}
	
	
	public ArrayList <Boolean> getAtribuicao () {
		if (atribuicoes.size() > 0) {
				Iterator <ArrayList <Boolean>> iterator = atribuicoes.iterator();
				if (iterator.hasNext()) {
					return iterator.next();
				} else {
					return null;
			}
		} else {
			return null;
		}
	}
	
	public boolean acaoDisponivel (Acao a) {
		boolean aplicavel = false;
		for (int i = 0; i < acoesDisponiveis.size(); i++) {
			if (acoesDisponiveis.get(i).getNome().equals(a.getNome())) {
				aplicavel = true;
				return aplicavel;
			}
		}
		return aplicavel;
	}

	public boolean isCarregado() {
		return carregado;
	}

	public void setCarregado(boolean carregado) {
		this.carregado = carregado;
	}

	public void setSmallB(double b) {
		this.b = b;
	}
	
	public double getSmallB () {
		return b;
	}

	@Override
	public Object clone() throws CloneNotSupportedException {
		Estado estadoClonado = new Estado(this.getNome());
		estadoClonado.setRecompensa(this.getRecompensa());
		for (int i = 0; i < this.getAcoesDisponiveis().size(); i++) {
			estadoClonado.adicionaAcao(this.getAcoesDisponiveis().get(i));
		}
		estadoClonado.setFuncaoValor(new ArrayList <Float>());
		
		estadoClonado.setAcaoOtima(null);
		estadoClonado.setResolvido(false);
		estadoClonado.setAgregado(false);
		estadoClonado.setSoma(0.0f);
		estadoClonado.setSmallB(0.0f);
		estadoClonado.setCarregado(false);
		estadoClonado.setAtribuicoes(new HashSet<ArrayList<Boolean>>(this.getAtribuicoes()));
		return estadoClonado;
	}

	public int getHorizonte() {
		return horizonte;
	}

	public void setHorizonte(int horizonte) {
		this.horizonte = horizonte;
	}

	public void removeAcaoSuperflua(Acao acao) {
		boolean acaoSuperflua = false;
		for (int i = 0; i < acoesDisponiveis.size(); i++) {
			Acao auxiliar = acoesDisponiveis.get(i);
			if (!acao.getNome().equals(auxiliar.getNome())) {
				if (auxiliar.getRecompensa() >= acao.getRecompensa()) {
					ArrayList <Transicao> transicoesAuxiliar = auxiliar.getTransicoes();
					ArrayList <Transicao> transicoesAcao = acao.getTransicoes();
					if (transicoesAuxiliar.size() == transicoesAcao.size()) {
						for (int j = 0; j < transicoesAuxiliar.size(); j++) {
							Transicao tAuxiliar = transicoesAuxiliar.get(j);
							Transicao tAcao = transicoesAcao.get(j);
							if (!tAuxiliar.equals(tAcao)) {
								continue;
							}
						}
						
						System.out.println("A��o " + acao.getNome() + " eh superflua.");
						acaoSuperflua = true;
						break;
					} else {
						continue;
					}
				} else {
					continue;
				}
			}
		}
		
		if (acaoSuperflua) {
			acao.getTransicoes().clear();
			acao.setRecompensa(-Float.MAX_VALUE);
		}
	}
	
}
