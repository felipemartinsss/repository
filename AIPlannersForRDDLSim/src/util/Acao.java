package util;

import java.util.ArrayList;

/**
 * Representa uma acao em um MDP.
 * @author fmsantos
 */
public class Acao {

    private String nome;

    private ArrayList <Transicao> transicoes;
    
    private float recompensa;

    private float q;

    /**
     * Construtor. Recebe o nome da ação.
     * @param nome
     */
    public Acao(String nome) {
        transicoes = new ArrayList <Transicao> ();
        recompensa = 0.0f;
        q = 0.0f;
        this.nome = nome;
    }
    
    /**
     * Construtor. Recebe o nome e uma recompensa para a ação a ser instanciada. Valor
     * da recompensa varia de acordo com o estado ao qual a ação pertence.
     * @param nome
     * @param recompensa
     */
    public Acao(String nome, float recompensa) {
        transicoes = new ArrayList <Transicao> ();
        this.recompensa = recompensa;
        q = 0.0f;
        this.nome = nome;
    }

    /**
     * Construtor. Recebe o nome da ação, uma recompensa para a ação a ser instanciada
     * e as transições geradas pela ação quando aplicada em um estado origem. Valor
     * da recompensa varia de acordo com o estado ao qual a ação pode ser aplicada.
     * @param nome
     * @param recompensa
     */
    public Acao(String nome, Float recompensa, ArrayList <Transicao> transicoes) {
        this.nome = nome;
        this.transicoes = transicoes;
        this.recompensa = recompensa;
    }

    /**
     * Obtém o nome da ação.
     * @return
     */
    public String getNome() {
        return this.nome;
    }


    /**
     * Obtém a recompensa da ação atual para o estado ao qual a instância da ação pertence.
     * @return
     */
    public float getRecompensa() {
        return recompensa;
    }

    @Override
    public String toString() {
        return this.nome; 
    }

    /**
     * Ajusta o valor da recompensa.
     * @param recompensa
     */
    public void setRecompensa (float recompensa) {
        this.recompensa = recompensa;
    }

    /**
     * Adiciona uma nova transição à ação atual.
     * @param t
     * @return
     */
    public boolean adicionaTransicao (Transicao t) {
        boolean resultado = transicoes.add (t);
        return resultado;
    }

    /**
     * Obtém a lista de transições da ação atual quando aplicada em um estado atual.
     * @return
     */
    public ArrayList <Transicao> getTransicoes () {
        return transicoes;
    }
    
    public void setTransicoes (ArrayList <Transicao> transicoes) {
    	this.transicoes = transicoes;
    }

    /**
     * Ajusta o valor Q(s,a).
     * @param q
     */
    public void setQ (float q) {
        this.q = q;
    }
    
    /**
     * Obtém o valor Q(s,a).
     *@return
     */
    public float getQ () {
        return q;
    }

    /**
     * Verifica se a ação atual é igual a uma outra ação. 
     * São iguais se seus nomes forem iguais.
     */
    public boolean equals(Object outraAcao) {
    	if (outraAcao instanceof Acao) {
    		Acao acao = (Acao) outraAcao;
    		if (this.nome.equals(acao.getNome())) {
                return true;
            } else {
                return false;
            }
    	} else {
    		return false;
    	}
    }
    
    /**
     * Devolve o código hash de uma ação.
     */
    @Override
    public int hashCode() {
    	return this.getNome().hashCode();
    }
}
