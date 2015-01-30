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

    // Utilizada em implementações do algoritmo LRTDP.
    private boolean resolvido;
    
    // Utilizada em implementações de agregação.
    private boolean agregado;
    
    // Utilizada em implementações de agregação. Soma do estado atual com relação a
    // estado e ação atual.
    private float soma;
    
    // Define atribuição de variáveis de estado que representa o estado atual.
    // Se atribuicoes.size() == 0, há um único estado.
    // Se atribuicoes.size() >= 1, o estado representa um estado abstrato proveniente de vários outros estados.
    private HashSet <ArrayList <Boolean>> atribuicoes;
    
    private boolean carregado = false;

	private double b;
	
	private int horizonte;

    /**
     * Verifica se o estado atual pertence ou não a algum estado agregado.
     * @return
     */
    public boolean isAgregado() {
		return agregado;
	}

    /**
     * Ajusta agregado para true se o estado atual pertence a algum estado agregado
     * e para false caso contrário.
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
     * Obtém o nome do estado atual.
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
     * Adiciona uma ação ao conjunto de ações aplicáveis do estado atual.
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
     * Obtém o número de ações aplicáveis no estado atual.
     * @return
     */
    public int getNumAcoesDisponiveis() {
        return acoesDisponiveis.size();
    }

    /**
     * Obtém a recompensa do estado atual quando trabalhamos com R(s) ao invés de R(s,a).
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
     * Obtém as ações aplicáveis no estado atual.
     * @return the acoesDisponiveis
     */
    public ArrayList <Acao> getAcoesDisponiveis() {
        return acoesDisponiveis;
    }

    /**
     * Obtém a i-ésima ação aplicável no estado atual.
     * @param i
     * @return
     */
    public Acao getAcaoDisponivel(int i) {
        return acoesDisponiveis.get(i);
    }

    /**
     * Obtém true se o estado atual já convergiu e false caso contrário.
     * @return
     */
    public boolean isResolvido() {
        return resolvido;
    }

    /**
     * Define o estado atual como resolvido (valor = true) ou não resolvido (valor = false).
     * @param valor
     */
    public void setResolvido (boolean valor) {
        this.resolvido = valor;
    }

    /**
     * Obtém a função valor no estado atual do estágio 0 até o último estágio calculado.
     * @return the funcaoValor
     */
    public ArrayList<Float> getFuncaoValor() {
        return funcaoValor;
    }

    /**
     * Ajusta a função valor com uma lista de valores para o estado atual.
     * @param funcaoValor the funcaoValor to set
     */
    public void setFuncaoValor(ArrayList<Float> funcaoValor) {
        this.funcaoValor = funcaoValor;
    }

    /**
     * Insere um novo valor para o último estágio calculado da função valor no estado atual.
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
     * Obtém o número de atualizações já realizadas para o estado atual.
     * @return
     */
    public int getNumAtualizacoesFuncaoValor () {
        return funcaoValor.size();
    }

    /**
     * Obtém o último valor da função valor calculada para o estado atual.
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
     * Calcula o residual do estado atual considerando q como último valor e o último
     * valor da função como se fosse o penúltimo.
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
        	// System.out.println("Estado " + this.getNome() + " ainda não foi atualizado vezes o suficiente.");
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
     * Obtém a ação ótima do estado atual.
     * @return the acaoOtima
     */
    public Acao getAcaoOtima() {
        return acaoOtima;
    }

    /**
     * Ajusta a ação ótima do estado atual.
     * @param acaoOtima the acaoOtima to set
     */
    public void setAcaoOtima(Acao acaoOtima) {
        this.acaoOtima = acaoOtima;
    }

    /**
     * Obtém uma ação aplicável no estado atual a partir de seu nome.
     * Se a ação não existe, cria a ação.
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
     * Verifica se o estado atual é igual a algum outro estado.
     * Dois estado são iguais se têm o mesmo nome.
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
     * Obtém o código hash do estado atual.
     */
    @Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.nome != null ? this.nome.hashCode() : 0) + horizonte * 117;
        return hash;
    }

    /**
     * Obtém a soma do estado atual.
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
	 * Obtém a atribuição de variáveis de estado que representa o estado atual.
	 * @return
	 */
	public HashSet<ArrayList <Boolean>> getAtribuicoes() {
		return atribuicoes;
	}

	/**
	 * Ajusta a atribuição das variáveis de estado necessárias para representa o estado atual.
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
						
						System.out.println("Ação " + acao.getNome() + " eh superflua.");
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
