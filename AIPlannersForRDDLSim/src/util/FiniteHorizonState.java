package util;

import util.Estado;

public class FiniteHorizonState {
	private Estado estado;
	private Integer horizon;
	
	public FiniteHorizonState (Estado estado, Integer horizon) {
		this.estado = estado;
		this.horizon = horizon;
	}
	
	public Integer getHorizon() {
		return horizon;
	}

	public void setHorizon(Integer horizon) {
		this.horizon = horizon;
	}


	
    public boolean equals (Object outroEstado) {
        if (outroEstado instanceof FiniteHorizonState) {
        	FiniteHorizonState e = ((FiniteHorizonState) outroEstado);
            if (this.getEstado().equals(e.getEstado().getNome()) && this.getHorizon() == e.getHorizon()) {
                return true;
            } else {
                return false;
            }
        } else {
            return false;
        }

    }
    
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.getEstado().getNome() != null ? this.getEstado().getNome().hashCode() * this.getHorizon() * 101 : 0);
        return hash;
    }

	public Estado getEstado() {
		return estado;
	}

	public void setEstado(Estado estado) {
		this.estado = estado;
	}
    
}
