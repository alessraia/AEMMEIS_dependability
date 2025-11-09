package model.libroService;

import java.util.List;
import java.util.Objects;

public class Reparto {
    //@ spec_public
    private int idReparto;

    //@ spec_public
    private String nome;

    //@ spec_public
    private String descrizione;

    //@ spec_public
    private String immagine;

    //@ spec_public
    private List<Libro> libri;

    //@ public invariant idReparto >= 0;

    //@ ensures \result >= 0;
    //@ pure
    public int getIdReparto() {
        return idReparto;
    }

    //@ requires idReparto >= 0;
    //@ assignable this.idReparto;
    //@ ensures this.idReparto == idReparto;
    public void setIdReparto(int idReparto) {
        this.idReparto = idReparto;
    }

    //@ ensures \result != null;
    //@ pure
    public String getDescrizione() {
        return descrizione;
    }

    //@ requires descrizione != null;
    //@ assignable this.descrizione;
    //@ ensures this.descrizione == descrizione;
    public void setDescrizione(String descrizione) {
        this.descrizione = descrizione;
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

    //@ also
    //@ requires o != null;
    //@ ensures \result ==> (o instanceof Reparto);
    //@ pure
    @Override
    public boolean equals(Object o) { //per il metodo contains
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Reparto reparto = (Reparto) o;
        return idReparto == reparto.idReparto && descrizione.equals(reparto.descrizione);
    }

    //@ ensures \result != null;
    //@ pure
    public String getNome() {
        return nome;
    }

    //@ requires nome != null;
    //@ assignable this.nome;
    //@ ensures this.nome == nome;
    public void setNome(String nome) {
        this.nome = nome;
    }

    //@ ensures \result != null;
    //@ pure
    public String getImmagine() {
        return immagine;
    }

    //@ assignable this.immagine;
    //@ ensures this.immagine == immagine;
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }
}
