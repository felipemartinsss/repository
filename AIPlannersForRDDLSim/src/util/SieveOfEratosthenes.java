package util;

import java.util.ArrayList;
import java.util.LinkedHashMap;

/**
 * This is a Sieve of Eratosthenes implementation.
 * It is used to generate prime numbers during model reductions, that is,
 * MRFS and ReachMRFS based planners.
 * To learn more about it: http://en.wikipedia.org/wiki/Sieve_of_Eratosthenes
 * @author felipemartinsss
 *
 */
public class SieveOfEratosthenes {
	private int oldLastValue;
	private int lastValue;
	private int missingPrimes = 0;
	private LinkedHashMap <Integer, Boolean> mappingOfNumbers;
	
	public SieveOfEratosthenes(int lastValue) {
		this.lastValue = lastValue;
	}
	
	public LinkedHashMap <Integer, Boolean> getMappingOfNumbers() {
		mappingOfNumbers = new LinkedHashMap <Integer, Boolean> ();
		Boolean TRUE = new Boolean (true);
		Boolean FALSE = new Boolean (false);
		
		for (int i = 2; i <= lastValue; i++) {
			mappingOfNumbers.put(i, TRUE);
		}
		
		
		double limite = Math.floor(Math.sqrt(lastValue));
		for (int i = 2; i <= limite; i++) {
			if (mappingOfNumbers.get(i).equals(TRUE)) {
				for (int j = (int) Math.pow(i, 2), k = 0; j <= lastValue; j = (int) Math.pow(i, 2) + k * i, k++) {
					mappingOfNumbers.put(j, FALSE);
				}
			}
		}
		
		return mappingOfNumbers;
	}
	
	
	public LinkedHashMap <Integer, Boolean> recomputeMappingOfNumbers() {
		if (mappingOfNumbers == null) {
			mappingOfNumbers = new LinkedHashMap <Integer, Boolean> ();
		}
		setLastValue(lastValue * 5);
		
		
		Boolean TRUE = new Boolean (true);
		Boolean FALSE = new Boolean (false);
		
		for (int i = oldLastValue; i <= lastValue; i++) {
			if (!mappingOfNumbers.containsKey(i)) {
				mappingOfNumbers.put(i, TRUE);
			}
		}
		
		
		double limite = Math.floor(Math.sqrt(lastValue));
		for (int i = 2; i <= limite; i++) {
			if (mappingOfNumbers.get(i).equals(TRUE)) {
				for (int j = (int) Math.pow(i, 2), k = 0; j <= lastValue; j = (int) Math.pow(i, 2) + k * i, k++) {
					mappingOfNumbers.put(j, FALSE);
				}
			}
		}
		return mappingOfNumbers;
	}
	
	public ArrayList <Integer> getPrimeNumbers (LinkedHashMap <Integer, Boolean> mappingOfNumbers) {
		ArrayList <Integer> primeNumbers = new ArrayList <Integer> ();
		for (Integer number : mappingOfNumbers.keySet()) {
			if (mappingOfNumbers.get(number).equals(true)) {
				primeNumbers.add(number);
			}
		}
		return primeNumbers;
	}
	
	public void printPrimeNumbers (LinkedHashMap <Integer, Boolean> mappingOfNumbers) {
		System.out.println("Prime numbers:");
		for (Integer number : mappingOfNumbers.keySet()) {
			if (mappingOfNumbers.get(number).equals(true)) {
				System.out.println(number);
			}
		}
		
	}

	public int getLastValue() {
		return lastValue;
	}

	public void setLastValue(int lastValue) {
		oldLastValue = this.lastValue;
		this.lastValue = lastValue;
	}

	public void suggestToFreeMemory() {
		mappingOfNumbers.clear();
		mappingOfNumbers = null;
		System.gc();
	}
	
	public int countPrimesUsed (LinkedHashMap <Integer, Boolean> primeUsed) {
		int countPrimesUsed = 0;
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				countPrimesUsed++;
			}
		}
		return countPrimesUsed;
	}
	
	public Integer getNextFreePrime (LinkedHashMap <Integer, Boolean> primeUsed) {
		Integer freePrime = null;
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(false)) {
				primeUsed.put(prime, true);
				freePrime = prime;
				break;
			}
		}
		
		if (freePrime == null) {
			missingPrimes++;
			System.out.println("N�o foi poss�vel prosseguir, poucos n�meros primos encontrados.");
			ArrayList <Integer> primeNumbers = this.getPrimeNumbers(this.recomputeMappingOfNumbers());
			System.out.println("Mais numeros primos foram encontrados.");
			for (Integer prime : primeNumbers) {
				if (!primeUsed.keySet().contains(prime)) {
					primeUsed.put(prime, false);
				}
			}
			freePrime = getNextFreePrime (primeUsed);
		}
		return freePrime;
	}
	
	public void freeAllPrimes (LinkedHashMap <Integer, Boolean> primeUsed) {
		for (Integer prime : primeUsed.keySet()) {
			if (primeUsed.get(prime).equals(true)) {
				primeUsed.put(prime, false);
			} else {
				break;
			}
		}
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		SieveOfEratosthenes soe = new SieveOfEratosthenes(10000000);
		LinkedHashMap <Integer, Boolean> mappingOfNumbers = soe.getMappingOfNumbers();
		// soe.printPrimeNumbers (mappingOfNumbers);
		ArrayList <Integer> primeNumbers = soe.getPrimeNumbers (mappingOfNumbers);
		// System.out.println("Prime Numbers:");
		// for (int i = 0; i < primeNumbers.size(); i++) {
		// 	System.out.println(primeNumbers.get(i));
		// }
		System.out.println("Prime numbers found. How many? " + primeNumbers.size());
		
		soe.setLastValue(soe.getLastValue() * 2);
		mappingOfNumbers = null;
		primeNumbers = null;
		System.gc();
		mappingOfNumbers = soe.recomputeMappingOfNumbers();
		primeNumbers = soe.getPrimeNumbers (mappingOfNumbers);
		
		System.out.println("Prime numbers found. How many? " + primeNumbers.size());
	}

}
