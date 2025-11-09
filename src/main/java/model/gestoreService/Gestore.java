package model.gestoreService;

/*@ nullable_by_default @*/
public class Gestore {
    //@ spec_public
    private String matricola;
    //@ spec_public
    private double stipendio;

    /*@
      @ public normal_behavior
      @   ensures \result == this.matricola;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getMatricola() {
        return matricola;
    }

    /*@
      @ public normal_behavior
      @   requires matricola != null && !matricola.isEmpty();
      @   assignable this.matricola;
      @   ensures this.matricola == matricola;
      @*/
    public void setMatricola(String matricola) {
        this.matricola = matricola;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.stipendio;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ double getStipendio() {
        return stipendio;
    }

    /*@
      @ public normal_behavior
      @   requires stipendio >= 0;
      @   assignable this.stipendio;
      @   ensures this.stipendio == stipendio;
      @*/
    public void setStipendio(double stipendio) {
        this.stipendio = stipendio;
    }
}
