package model.ordineService;

import model.libroService.Libro;

/*@ nullable_by_default @*/
public class RigaOrdine {
    //@ spec_public
    private String idOrdine;
    //@ spec_public
    private Libro libro;
    //@ spec_public
    private double prezzoUnitario;
    //@ public invariant prezzoUnitario >= 0.0;

    //@ spec_public
    private int quantita;
    //@ public invariant quantita >= 1;

    /*@ public normal_behavior
      @   ensures \result == idOrdine;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getIdOrdine() {
        return idOrdine;
    }

    /*@ public normal_behavior
      @   assignable this.idOrdine;
      @   ensures this.idOrdine == idOrdine;
      @*/
    public void setIdOrdine(String idOrdine) {
        this.idOrdine = idOrdine;
    }

    /*@ public normal_behavior
      @   ensures \result == libro;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ Libro getLibro() {
        return libro;
    }

    /*@ public normal_behavior
      @   assignable this.libro;
      @   ensures this.libro == libro;
      @*/
    public void setLibro(Libro libro) {
        this.libro = libro;
    }

    /*@ public normal_behavior
      @   ensures \result == prezzoUnitario;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ double getPrezzoUnitario() {
        return prezzoUnitario;
    }

    /*@ public normal_behavior
      @   requires prezzo >= 0.0;
      @   assignable this.prezzoUnitario;
      @   ensures this.prezzoUnitario == prezzo;
      @*/
    public void setPrezzoUnitario(double prezzoUnitario) {
        this.prezzoUnitario = prezzoUnitario;
    }

    /*@ public normal_behavior
      @   ensures \result == quantita;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getQuantita() {
        return quantita;
    }

    /*@ public normal_behavior
      @   requires quantita >= 1;
      @   assignable this.quantita;
      @   ensures this.quantita == quantita;
      @*/
    public void setQuantita(int quantita) {
        this.quantita = quantita;
    }
}
