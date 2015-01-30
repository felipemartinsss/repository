package util;

/**
 * Representa as transições de uma ação.
 * @author fmsantos
 */
public class Transicao implements Comparable <Transicao> {
    private String origem;
    private String destino;
    private float probabilidade;
    private float recompensa;

    /** Construtor padrão.
     */
    public Transicao() {

    }

    /**
     * Recebe uma origem, um destino, uma probabilidade e uma recompensa para representar
     * a transição atual.
     * As recompensas de uma transição deverão ser sempre as mesmas para cada par (s,a), independentemente
     * de s' (destino).
     * @param origem
     * @param destino
     * @param probabilidade
     * @param recompensa
     */
    public Transicao (String origem, String destino, float probabilidade, float recompensa) {
        this.origem = origem;
        this.destino = destino;
        this.probabilidade = probabilidade;
        this.recompensa = recompensa;
    }
    
    /**
     * Obtém o nome do estado que origina a transição.
     * @return the origem
     */
    public String getOrigem() {
        return origem;
    }

    /**
     * Ajusta o nome do estado que origina a transição.
     * @param origem the origem to set
     */
    public void setOrigem(String origem) {
        this.origem = origem;
    }

    /**
     * Obtém o nome do estado de destino da transição.
     * @return the destino
     */
    public String getDestino() {
        return destino;
    }

    /**
     * Ajusta o nome do estado de destino da transição.
     * @param destino the destino to set
     */
    public void setDestino(String destino) {
        this.destino = destino;
    }

    /**
     * Obtém a probabilidade da transição atual: (s, a, s').
     * @return the probabilidade
     */
    public float getProbabilidade() {
        return probabilidade;
    }

    /**
     * Ajusta a probabilidade da transição atual: (s, a, s').
     * @param probabilidade the probabilidade to set
     */
    public void setProbabilidade(float probabilidade) {
        this.probabilidade = probabilidade;
    }
    
    /**
     * Converte uma transição para String utilizando a notação: P(s',s) = p.
     */
    public String toString() {
    	return "P(" + destino + "|" + origem + ", a)" + " = " + probabilidade;  
    }

    /**
     * Obtém o valor da recompensa para o par (s,a).
     * @return
     */
	public float getRecompensa() {
		return recompensa;
	}

	/**
	 * Ajusta o valor da recompensa para o par (s,a).
	 * @param recompensa
	 */
	public void setRecompensa(float recompensa) {
		this.recompensa = recompensa;
	}

	/**
	 * Permite a ordenação de transições de uma ação com base
	 * na probabilidade de ser a transição realizada.
	 * Exemplo: 0.1, 0.1, 0.3, 0.5 (Observe que as transições somam 1).
	 */
	@Override
	public int compareTo(Transicao outraTransicao) {
		Transicao t2 = (Transicao) outraTransicao;
		if (getProbabilidade() > t2.getProbabilidade()) {
			return 1;
		} else if (getProbabilidade() == t2.getProbabilidade()) {
			return 0;
		} else {
			return -1;
		}
	}
	
	@Override
	public boolean equals(Object outraTransicao) {
		if (outraTransicao instanceof Transicao) {
			Transicao outra = (Transicao) outraTransicao;
			if (this.getOrigem().equals(outra.getOrigem())) {
				if (this.getDestino().equals(outra.getDestino())) {
					if (this.getProbabilidade() == outra.getProbabilidade()) {
						// if (this.getRecompensa() == outra.getRecompensa()) {
						return true;
						// }
					}
				}
			}
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		int hashCode = this.getOrigem().hashCode() * this.getDestino().hashCode() * 17;
		return hashCode;
	}
}
