package util;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

/**
 * Class that is used to store statistical information in files after 
 * computing a policy using our planners.
 * @author felipemartinsss
 *
 */
public class GeradorDeArquivo {
	
	private StringBuffer conteudo;
	
	public GeradorDeArquivo (StringBuffer conteudo) {
		this.conteudo = conteudo;
	}
	
	public void geraArquivo (String nomeArquivo) {
		File f = new File (nomeArquivo);
		FileWriter fw = null;
		PrintWriter pw = null;
		try {
			fw = new FileWriter (f, true);
			pw = new PrintWriter (fw);
			pw.write(conteudo.toString());
			pw.close();
			fw.close();
			System.out.println("File " + f.getAbsolutePath() + " generated.");
		} catch (IOException e) {
			System.out.println("Erro ao escrever em arquivo: " + f.getAbsolutePath());
			e.printStackTrace();
		}
	}
	
	public void adiciona (StringBuffer conteudoAdicional) {
		this.conteudo.append(conteudoAdicional);
	}
	
	/**
	 * Need to replace this class by LOG4J.
	 * @param msg
	 * @throws IOException
	 */
	public void writeToLog(boolean LOG_CONVERGENCE, String LOG_FILE, String OS, String msg) throws IOException {
		if (LOG_CONVERGENCE) {
			BufferedWriter bw = new BufferedWriter(new FileWriter(LOG_FILE + OS + ".log" , true));
			bw.write(msg);
			bw.newLine();
			bw.flush();
			bw.close();
		}
	}
	
}
