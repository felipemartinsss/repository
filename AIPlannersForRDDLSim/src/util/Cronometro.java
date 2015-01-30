package util;

import java.util.Scanner;

/**
 * Class that represents a cronometer that gives time in the following format: hours h, minutes min, seconds s, miliseconds ms.
 * @author Felipe
 *
 */
public class Cronometro {
	private long dias;
	private long milisegundos;
	private long horas;
	private long minutos;
	private long segundos;
	private long start;
	private long end;
	private long totalMilisegundos;
	
	/**
	 * Computer the interval of time between execution begin and end.
	 */
	public void calculaIntervalo() {
		milisegundos = end - start;
		totalMilisegundos = milisegundos;
		dias = milisegundos / 86400000;
		milisegundos = milisegundos % 86400000;
		horas = milisegundos / 3600000;
		milisegundos = milisegundos % 3600000;
		minutos = milisegundos / 60000;
		milisegundos = milisegundos % 60000;
		segundos = milisegundos / 1000;
		milisegundos = milisegundos % 1000;
	}
	
	/**
	 * Returns a string with execution interval.
	 * @return
	 */
	public String getIntervalo() {
		return "" + dias + " d " + horas + " h " 
							   + minutos + " min " 
				               + segundos + " s "
				               + milisegundos + " ms \n";
	}
	
	/**
	 * Get time in milliseconds.
	 * @return
	 */
	public long getMilisegundos() {
		return milisegundos;
	}
	
	/**
	 * Get hours of execution after computation of a time interval.
	 * @return
	 */
	public long getHoras() {
		return horas;
	}
	
	/**
	 * Get minutes of execution after computation of a time interval.
	 * @return
	 */
	public long getMinutos() {
		return minutos;
	}
	
	/**
	 * Get the seconds of execution after the computation of a time interval.
	 * @return
	 */
	public long getSegundos() {
		return segundos;
	}
	
	/**
	 * Get the initial time in milliseconds by the last time that the cronometer was started.
	 * @return
	 */
	public long getStart() {
		return start;
	}
	
	/**
	 * Starts the cronometer.
	 */
	public void setStart() {
		this.start = System.currentTimeMillis();
	}
	
	/**
	 * Get the instant in which the cronometer was stopped by the last time.
	 * @return
	 */
	public long getEnd() {
		return end;
	}
	
	/**
	 * Stops the cronometer and computes the execution interval.
	 */
	public void setEnd() {
		this.end = System.currentTimeMillis();
		calculaIntervalo();
	}
	
	/**
	 * Returns the total time in milliseconds.
	 * @return
	 */
	public long getTotalMilisegundos () {
		return totalMilisegundos;
	}

	/**
	 * Sets the total time in milliseconds.
	 * @return
	 */
	private void setMilisegundos(long nextLong) {
		this.milisegundos = nextLong;
	}

	/**
	 * Computes the time of execution in format DD:
	 * @return
	 */
	private String converteParaHMS() {
		dias = milisegundos / 86400000;
		milisegundos = milisegundos % 86400000;
		horas = milisegundos / 3600000;
		milisegundos = milisegundos % 3600000;
		minutos = milisegundos / 60000;
		milisegundos = milisegundos % 60000;
		segundos = milisegundos / 1000;
		milisegundos = milisegundos % 1000;
		return getIntervalo();
	}
	
	// Main method for test purposes.
	public static void main (String[] args) {
		Cronometro c = new Cronometro();
		Scanner sc = new Scanner(System.in);
		System.out.println ("Entre com o tempo em milisegundos:");
		c.setMilisegundos(sc.nextLong());
		System.out.println ("Entre com o numero de rodadas: ");
		c.setMilisegundos(c.getMilisegundos() / sc.nextInt());
		System.out.println (c.converteParaHMS ());
		
	}
	
	
}
