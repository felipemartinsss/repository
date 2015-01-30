package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;

public class BisimulationStatistics {
	private String instanceName;
	private boolean computeStandardDeviation = false;
	
	private ArrayList <String> readFile (String fileName) {
		File file = new File(fileName);
		if (file.exists()) {
			ArrayList <String> fileContent = null;
			FileReader fileReader = null;
			BufferedReader bufferedReader = null;
			try {
				fileReader = new FileReader(file);
				bufferedReader = new BufferedReader(fileReader);
				fileContent = new ArrayList <String>();
				String line;
				while ((line = bufferedReader.readLine()) != null) {
					fileContent.add(line);
				}
				
				bufferedReader.close();
				fileReader.close();
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return fileContent;
		} else {
			System.out.printf("File %s not found.\n", fileName);
			return null;
		}
	}
	
	
	
	private HashMap <String, ArrayList <Double>> parseFile (ArrayList <String> fileContent) {
		HashMap <String, ArrayList <Double>> fileData = new HashMap <String, ArrayList <Double>>();
		for (String line : fileContent) {
			String[] tokens = line.split("=");
			if (tokens.length == 2) {
				if (!tokens[0].equals("INSTANCE")) {
					if (!fileData.containsKey(tokens[0])) {
						ArrayList <Double> values = new ArrayList <Double>();
						values.add(new Double(tokens[1]));
						fileData.put(tokens[0], values);
					} else {
						ArrayList <Double> values = fileData.get(tokens[0]);
						values.add(new Double(tokens[1]));
						fileData.put(tokens[0], values);
					}
				} else {
					instanceName = tokens[1];
				}
			}
		}
		return fileData;
	}
	
	private LinkedHashMap <String, Double> computeDataAverage (HashMap <String, ArrayList<Double>> fileData) {
		LinkedHashMap <String, Double> dataAverage = new LinkedHashMap <String, Double>();
		for (String field : fileData.keySet()) {
			ArrayList <Double> values = fileData.get(field);
			double valuesSize = values.size();
			double sum = 0.0d;
			for (int i = 0; i < valuesSize; i++) {
				sum += values.get(i);
			}
			double average = sum / valuesSize; 
			dataAverage.put(field, average);
		}
		return dataAverage;
	}
	
	private void computeAdditionalStatistics (HashMap <String, ArrayList<Double>> fileData, LinkedHashMap <String, Double> dataAverage) {
		ArrayList <Double> totalTimeList = fileData.get("TOTAL_TIME");
		Double totalTimeAverage;
		if (totalTimeList != null) {
			totalTimeAverage = dataAverage.get("TOTAL_TIME");
			
		} else {
			totalTimeList = fileData.get("PLANNER_TIME");
			totalTimeAverage = dataAverage.get("PLANNER_TIME");
		}
		Double sumOfSquares = 0.0d;
		Double numberOfExperiments = 0.0d;
		for (Double totalTime : totalTimeList) {
			sumOfSquares += Math.pow(totalTime - totalTimeAverage, 2);
			numberOfExperiments += 1.0d;
		}
		
		Double variance = sumOfSquares / numberOfExperiments;
		Double totalTimeStandardDeviation = Math.sqrt(variance);
		Double totalTimeStandardError = totalTimeStandardDeviation / Math.sqrt(numberOfExperiments); 
		dataAverage.put("TOTAL_TIME_VARIANCE", variance);
		dataAverage.put("TOTAL_TIME_STD_DEV", totalTimeStandardDeviation);
		dataAverage.put("TOTAL_TIME_STD_ERR", totalTimeStandardError);
		Double confidenceIntervalLowerBound = totalTimeAverage - 1.96 * totalTimeStandardError;
		Double confidenceIntervalUpperBound = totalTimeAverage + 1.96 * totalTimeStandardError;
		dataAverage.put("CONFIDENCE_INTERVAL_LB", confidenceIntervalLowerBound);
		dataAverage.put("CONFIDENCE_INTERVAL_UB", confidenceIntervalUpperBound);
	}
	
	private HashMap <String, Double> computeStandardDeviation (HashMap <String, ArrayList<Double>> fileData, 
			HashMap <String, Double> dataAverage) {
		HashMap <String, Double> standardDeviation = new HashMap <String, Double>();
	
		for (String field : fileData.keySet()) {
			ArrayList <Double> values = fileData.get(field);
			double valuesSize = values.size();
			double sum = 0.0d;
			Double fieldAverage = dataAverage.get(field);
			Double tempStandardDeviation = 0.0d;
			for (int i = 0; i < valuesSize; i++) {
				sum += Math.pow(values.get(i) - fieldAverage, 2.0d);
			}
			tempStandardDeviation = Math.sqrt(sum / (valuesSize - 1));
			standardDeviation.put(field, tempStandardDeviation);
		}
		return standardDeviation;
		
	}
	
	private StringBuffer dataToStringBuffer (HashMap <String, Double> dataAverage) {
		StringBuffer sb = new StringBuffer("");
		sb.append(instanceName + ",");
		for (String field : dataAverage.keySet()) {
			String average = "" + dataAverage.get(field);
			// average = average.replace(".", ",");
			sb.append(average + ",");
		}
		sb.append("\n");
		return sb;
	}
	
	
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		BisimulationStatistics bs = new BisimulationStatistics();
		String directoryName;
		if (args.length == 1) {
			directoryName = args[0];
			File directory  = new File (directoryName);
			if (!directory.isDirectory()) {
				System.out.println("A valid directory is needed.");
				System.exit(1);
			}
			File[] filesInDirectory = directory.listFiles();
			File averageFile = new File(directory + "/" + "statistics_" + directoryName + ".csv");
			for (int i = 0; i < filesInDirectory.length; i++) {
				if (filesInDirectory[i].isFile() && !filesInDirectory[i].getName().startsWith("statistics")) {
					String fileName = filesInDirectory[i].getName();
					ArrayList <String> fileContent = bs.readFile (directory + "/" + fileName);
					HashMap <String, ArrayList <Double>> fileData = bs.parseFile (fileContent);
					LinkedHashMap <String, Double> dataAverage = bs.computeDataAverage (fileData);
					bs.computeAdditionalStatistics(fileData, dataAverage);
					// HashMap <String, Double> standardDeviation = bs.computeStandardDeviation (fileData, dataAverage);
					// HashMap <String, Double> averageTotalTime = bs.computeTotalTime (dataAverage);
					if (!averageFile.exists()) {
						GeradorDeArquivo fileGenerator = new GeradorDeArquivo(bs.getHeaders(dataAverage));
						fileGenerator.geraArquivo(directory + "/" + "statistics_" + directoryName + ".csv");
					}
					
					GeradorDeArquivo fileGenerator = new GeradorDeArquivo(bs.dataToStringBuffer(dataAverage));
					// fileGenerator.adiciona(bs.dataToStringBuffer(standardDeviation);
					fileGenerator.geraArquivo(directory + "/" + "statistics_" + directoryName + ".csv");
					System.out.println("Averages computed for file " + fileName);
					
					
				}
			}
		} else {
			System.out.println("Parameters: directory filename");
			System.out.println("Current directory: " + new File(".").getAbsolutePath());
		}

	}



	private HashMap<String, Double> computeTotalTime(
			HashMap<String, Double> dataAverage) {
		double sum = 0.0d;
		for (String field : dataAverage.keySet()) {
			sum += dataAverage.get(field);
		}
		
		HashMap <String, Double> totalTime = new HashMap<String, Double> ();
		totalTime.put("TOTAL_TIME", sum);
		return totalTime;
	}



	private StringBuffer getHeaders(HashMap <String, Double> dataAverage) {
		StringBuffer sb = new StringBuffer("");
		
		// DEFINE CARACTERE , COMO SEPARADOR EM EXCEL.
		// sb.append("sep=,");
		// sb.append("\n");
		
		sb.append("INSTANCE,");
		for (String field : dataAverage.keySet()) {
			sb.append(field + ",");
		}
		
		sb.append("\n");
		return sb;
	}



	public String getInstanceName() {
		return instanceName;
	}



	public void setInstanceName(String instanceName) {
		this.instanceName = instanceName;
	}

}
