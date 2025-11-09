package model.carrelloService;

import model.libroService.Libro;
/*@ nullable_by_default @*/
public class RigaCarrello {
    //@ spec_public
    private String idCarrello;
    //@ spec_public
    private Libro libro;
    //@ spec_public
    private int quantita;

    /*@
      @ public normal_behavior
      @   ensures \result == this.idCarrello;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getIdCarrello() {
        return idCarrello;
    }

    /*@
      @ public normal_behavior
      @   requires idCarrello != null && !idCarrello.isEmpty();
      @   assignable this.idCarrello;
      @   ensures this.idCarrello == idCarrello;
      @*/
    public void setIdCarrello(String idCarrello) {
        this.idCarrello = idCarrello;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.libro;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Libro getLibro() {
        return libro;
    }

    /*@
      @ public normal_behavior
      @   requires libro != null;
      @   assignable this.libro;
      @   ensures this.libro == libro;
      @*/
    public void setLibro(Libro libro) {
        this.libro = libro;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.quantita;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getQuantita() {
        return quantita;
    }

    /*@
      @ public normal_behavior
      @   requires quantita >= 0;
      @   assignable this.quantita;
      @   ensures this.quantita == quantita;
      @*/
    public void setQuantita(int quantita) {
        this.quantita = quantita;
    }
}
