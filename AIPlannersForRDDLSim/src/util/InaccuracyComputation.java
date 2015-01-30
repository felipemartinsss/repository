package util;

import java.util.Scanner;

public class InaccuracyComputation {

	static double gamma = 0.99d;
	static final int horizon = 40;
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		Scanner sc = new Scanner (System.in);
		System.out.println("Digite a recompensa máxima:");
		double maxReward = sc.nextDouble();
		System.out.println("Digite a recompensa mínima:");
		double minReward = sc.nextDouble();
		
		double lowerBound = 0.0d;
		double upperBound = 0.0d;
		
		for (int i = 0; i < 40; i++) {
			lowerBound += Math.pow(gamma, i) * minReward;
			upperBound += Math.pow(gamma, i) * maxReward;
		}
		
		System.out.println("LowerBound Original MDP = " + lowerBound);
		System.out.println("UpperBound Original MDP = " + upperBound);
		System.out.println("Interval width: " + Math.abs(upperBound - lowerBound));
	}

}
