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
     * Construtor. Recebe o nome da a��o.
     * @param nome
     */
    public Acao(String nome) {
        transicoes = new ArrayList <Transicao> ();
        recompensa = 0.0f;
        q = 0.0f;
        this.nome = nome;
    }
    
    /**
     * Construtor. Recebe o nome e uma recompensa para a a��o a ser instanciada. Valor
     * da recompensa varia de acordo com o estado ao qual a a��o pertence.
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
     * Construtor. Recebe o nome da a��o, uma recompensa para a a��o a ser instanciada
     * e as transi��es geradas pela a��o quando aplicada em um estado origem. Valor
     * da recompensa varia de acordo com o estado ao qual a a��o pode ser aplicada.
     * @param nome
     * @param recompensa
     */
    public Acao(String nome, Float recompensa, ArrayList <Transicao> transicoes) {
        this.nome = nome;
        this.transicoes = transicoes;
        this.recompensa = recompensa;
    }

    /**
     * Obt�m o nome da a��o.
     * @return
     */
    public String getNome() {
        return this.nome;
    }


    /**
     * Obt�m a recompensa da a��o atual para o estado ao qual a inst�ncia da a��o pertence.
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
     * Adiciona uma nova transi��o � a��o atual.
     * @param t
     * @return
     */
    public boolean adicionaTransicao (Transicao t) {
        boolean resultado = transicoes.add (t);
        return resultado;
    }

    /**
     * Obt�m a lista de transi��es da a��o atual quando aplicada em um estado atual.
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
     * Obt�m o valor Q(s,a).
     *@return
     */
    public float getQ () {
        return q;
    }

    /**
     * Verifica se a a��o atual � igual a uma outra a��o. 
     * S�o iguais se seus nomes forem iguais.
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
     * Devolve o c�digo hash de uma a��o.
     */
    @Override
    public int hashCode() {
    	return this.getNome().hashCode();
    }
}
