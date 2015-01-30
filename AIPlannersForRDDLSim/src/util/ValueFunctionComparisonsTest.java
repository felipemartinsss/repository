package util;

import java.util.ArrayList;
import java.util.HashMap;

import com.sun.org.apache.xalan.internal.xsltc.runtime.Hashtable;

public class ValueFunctionComparisonsTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		ArrayList <Double> funcaoValorA = new ArrayList <Double> ();
		ArrayList <Double> funcaoValorB = new ArrayList <Double> ();
		HashMap <Integer, Double> mapaDeValores = new HashMap <Integer, Double> ();
		Hashtable tabelaHash = new Hashtable();
		
		int i = 0;
		
		funcaoValorA.add((double) i * 2);
		funcaoValorB.add((double) i * 2);
		
		System.out.println("ArrayList Test");
		if (funcaoValorA.get(i).equals(funcaoValorB.get(i))) {
			System.out.println("Are the numbers equals? true");
		} else {
			System.out.println("Are the numbers equals? false");
		}
		
		
		if (funcaoValorA.get(i) == funcaoValorB.get(i)) {
			System.out.println("Are the references equals? true");
		} else {
			System.out.println("Are the references equals? false");
		}
		
		mapaDeValores.put(1, (double) 1 * 2);
		mapaDeValores.put(2, (double) 1 * 2);
		
		System.out.println("HashMap Test");
		if (mapaDeValores.get(1).equals(mapaDeValores.get(2))) {
			System.out.println("Are the numbers equals? true");
		} else {
			System.out.println("Are the numbers equals? false");
		}
		
		if (mapaDeValores.get(1) == mapaDeValores.get(2)) {
			System.out.println("Are the references equals? true");
		} else {
			System.out.println("Are the references equals? false");
		}
		
		tabelaHash.put(1, 2);
		tabelaHash.put(1, 2);
		System.out.println("Hashtable Test");
		if (tabelaHash.get(1) == tabelaHash.get(2)) {
			System.out.println("Are the references equals? true");
		} else {
			System.out.println("Are the references equals? false");
		}
	}

}
