package model.libroService;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
/*@ nullable_by_default @*/
public class Sede {
    //@ spec_public
    private int idSede;

    //@ spec_public
    private String citta;

    //@ spec_public
    private String via;

    //@ spec_public
    private int civico;

    //@ spec_public
    private String cap;

    //@ spec_public
    private List<Libro> libri;

    //@ ensures \result >= 0;
    //@ pure
    public int getIdSede() {
        return idSede;
    }

    //@ requires idSede >= 0;
    //@ assignable this.idSede;
    //@ ensures this.idSede == idSede;
    public void setIdSede(int idSede) {
        this.idSede = idSede;
    }

    //@ ensures \result != null;
    //@ pure
    public String getCitta() {
        return citta;
    }

    //@ requires citta != null;
    //@ assignable this.citta;
    //@ ensures this.citta == citta;
    public void setCitta(String citta) {this.citta = citta;}

    //@ ensures \result != null;
    //@ pure
    public String getVia() {
        return via;
    }

    //@ requires via != null;
    //@ assignable this.via;
    //@ ensures this.via == via;
    public void setVia(String via) {
        this.via = via;
    }

    //@ ensures \result >= 0;
    //@ pure
    public int getCivico() {
        return civico;
    }

    //@ requires civico >= 0;
    //@ assignable this.civico;
    //@ ensures this.civico == civico;
    public void setCivico(int civico) {
        this.civico = civico;
    }

    //@ ensures \result != null;
    //@ pure
    public String getCap() {
        return cap;
    }

    //@ requires cap != null;
    //@ assignable this.cap;
    //@ ensures this.cap == cap;
    public void setCap(String cap) {
        this.cap = cap;
    }

    //@ also
    //@ requires o != null;
    //@ ensures \result ==> (o instanceof Sede);
    //@ pure
    @Override
    public boolean equals(Object o) { //per poter utilizzare il metodo contains
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Sede sede = (Sede) o;
        return idSede == sede.idSede && civico == sede.civico && citta.equals(sede.citta) && via.equals(sede.via) && cap.equals(sede.cap);
    }

    //@ ensures \result != null;
    //@ pure
    public List<Libro> getLibri() {
        return libri;
    }

    //@ requires libri != null;
    //@ assignable this.libri;
    //@ ensures this.libri == libri;
    public void setLibri(List<Libro> libri) {
        this.libri = libri;
    }
}
