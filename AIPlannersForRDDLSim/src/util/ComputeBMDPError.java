package util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.ArrayList;

public class ComputeBMDPError {
	
	private static ArrayList <String> readFile (String fileName) {
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
	

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		BisimulationStatistics bs = new BisimulationStatistics();
		String fileName;
		String fileName2;
		
		if (args.length == 2) {
			fileName = args[0];
			File fileOne  = new File (fileName);
			if (!fileOne.isFile()) {
				System.out.println("A valid file is needed.");
				System.exit(1);
			}
			
			fileName2 = args[1];
			File fileTwo  = new File (fileName2);
			if (!fileTwo.isFile()) {
				System.out.println("A valid file is needed.");
				System.exit(1);
			}
			
			ArrayList<String> fileOneContent = readFile(fileName);
			ArrayList<String> fileTwoContent = readFile(fileName2);
			Double exactValue = 0.0d;
			Double approximatedValue = 0.0d;
			String domainFileOne = null;
			String domainFileTwo = null;
			String epsilonValue = null;
			
			System.out.println("Exact value for s0");
			for (int i = 0; i < fileOneContent.size(); i++) {
				String currentLine = fileOneContent.get(i);
				if (currentLine.startsWith("INSTANCE=")) { 
					String[] parts = currentLine.split("=");
					domainFileOne = parts[1];
				}
				
				if (currentLine.startsWith("V*(s0)=")) {
					System.out.println(currentLine);
					String[] parts = currentLine.split("=");
					exactValue = Double.valueOf(parts[1]);
					break;
				}
			}
			
			System.out.println("Approximated value for s0");
			for (int i = 0; i < fileTwoContent.size(); i++) {
				String currentLine = fileTwoContent.get(i);
				
				if (currentLine.startsWith("INSTANCE=")) { 
					String[] parts = currentLine.split("=");
					domainFileTwo = parts[1];
				}
				
				if (currentLine.startsWith("EPSILON=")) { 
					String[] parts = currentLine.split("=");
					epsilonValue = parts[1];
				}
				
				if (currentLine.startsWith("V*(s0)=")) {
					System.out.println(currentLine);
					String[] parts = currentLine.split("=");
					approximatedValue = Double.valueOf(parts[1]);
					break;
				}
			}
			
			if (domainFileOne.equals(domainFileTwo)) {
				Double absolutDifference = Math.abs(exactValue - approximatedValue);
				Double absolutExactValue = Math.abs(exactValue);
				Double error = (absolutDifference / absolutExactValue) * 100.0d;
				File saida = new File ("BMDPErrors/errorsForDifferentEpsilons.txt");
				boolean fileExists = true;
				if (!saida.exists()) {
					fileExists = false;
				}
				try {
					BufferedWriter bw = new BufferedWriter(new FileWriter(saida.getAbsolutePath(), true));
					if (!fileExists) {
						bw.write("INSTANCE\tEPSILON\tERROR\n");
						bw.flush();
					}
					bw.write(domainFileOne + "\t" + epsilonValue + "\t" + error + "\n");
					bw.flush();
					bw.close();
				} catch (FileNotFoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
				// System.out.println("INSTANCE=" + domainFileOne);
				// System.out.println("EPSILON=" + epsilonValue);
				// System.out.println("%ErrorS0=" + error);
			} else {
				System.out.println("Instances are different.");
			}
		}
	}

}
