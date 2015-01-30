package util;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;

public class ExecutionTimeStatistics {
	
	private static ArrayList <Double> experimentsTime;

	public static double computeAverage () {
		double average = 0.0d;
		for (double d : experimentsTime) {
			average += d;
		}
		
		average /= experimentsTime.size();
		return average;
	}
	
	public static double computeStandardDeviation (double average) {
		double stdDev = 0.0d;
		for (double d : experimentsTime) {
			stdDev += Math.pow((d - average), 2);
		}
		
		stdDev /= (experimentsTime.size() - 1);
		stdDev = Math.sqrt(stdDev);
		return stdDev;
	}
	
	public static double computeStandardError (double avg, double stdDev) {
		double stdErr = 0.0d;
		stdErr = 1.96 * stdDev / Math.sqrt(experimentsTime.size());
		return stdErr;
	}
	
	public static void main(String[] args) throws FileNotFoundException {
		experimentsTime = new ArrayList <Double>();
		File f = new File (args[0]);
		Scanner sc = new Scanner  (f);
		while (sc.hasNextLine()) {
			String line = sc.nextLine();
			
			if (line.length() > 3 && line.startsWith("user")) {
				double totalTimeInSeconds = 0.0d;
				String[] time = line.split("\\t");			
				String minutes = (time[1].split("\\."))[0].split("m")[0];
				String seconds = (time[1].split("\\."))[0].split("m")[1];
				String miliseconds = (time[1].split("\\."))[1].substring(0, 3);
				totalTimeInSeconds = Integer.parseInt(minutes) * 60 + Integer.parseInt(seconds) + Double.parseDouble(miliseconds) / 1000.0d;
				experimentsTime.add(totalTimeInSeconds);
			}
			
		}
		
		sc.close();
		
		double avg = computeAverage();
		
		System.out.println("user AVG: " + avg);
		
		double stdDev = computeStandardDeviation(avg);
		
		System.out.println("user STD_DEV: " + stdDev);
		
		double stdErr = computeStandardError(avg, stdDev);
		
		System.out.println("user STD_ERR (95%): " + stdErr);
	}

}
