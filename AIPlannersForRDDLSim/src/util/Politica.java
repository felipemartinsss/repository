package util;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * Class that represents a policy S -> A
 * @author felipemartinsss
 */
public class Politica {
    private HashMap <Estado, Acao> mapa;

    /**
     * Construtor padr�o.
     */
    public Politica () {
        mapa = new HashMap <Estado, Acao> ();
    }

    /**
     * Adiciona um novo estado � pol�tica atual e ajusta a��o para null.
     * @param e
     */
    public void adicionaNovoEstado (Estado e) {
        mapa.put(e, null);
    }

    /**
     * Obt�m a a��o definida pela politica para o estado e.
     * @param e
     * @return
     */
    public Acao getAcao (Estado e) {
        return mapa.get(e);
    }

    /**
     * Define a a��o a ser aplicada em um estado e seguindo a pol�tica atual.
     * @param e
     * @param a
     */
    public void ajustaAcao (Estado e, Acao a) {
        mapa.put(e, a);
    }
    

    /**
     * Converte uma pol�tica para String exibindo todos os valores (pi(s) = a).
     */
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer("");

        sb.append("Politica MDP\n");
        HashSet <Estado> estados = new HashSet<Estado>(mapa.keySet());
        Iterator <Estado> iteradorEstados = estados.iterator();
        while (iteradorEstados.hasNext()) {
        	Estado e = iteradorEstados.next();
            Acao a = mapa.get(e);
            if (e != null && a != null) {
                sb.append("Pi(" + e.getNome() + ") = " + a.getNome() + "\n");
            }
        }
        return sb.toString();
    }
    
    public Set<Estado> getEstados() {
    	return mapa.keySet();
    }
    
}
