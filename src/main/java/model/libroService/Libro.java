package model.libroService;

import java.util.List;
import java.util.Objects;
/*@ nullable_by_default @*/
public class Libro {
    //@ spec_public
    private String isbn;

    //@ spec_public
    private String titolo;

    //@ spec_public
    private String genere;

    //@ spec_public
    private String annoPubblicazioni;

    //@ spec_public
    private double prezzo;

    //@ spec_public
    private int sconto;

    //@ spec_public
    private String trama;

    //@ spec_public
    private String immagine;

    //@ spec_public
    private boolean disponibile;

    //@ spec_public
    private List<Autore> autori;

    //@ public invariant prezzo >= 0;
    //@ public invariant sconto >= 0 && sconto <= 100;

    //@ ensures \result != null;
    //@ pure
    public String getTitolo() {
        return titolo;
    }

    //@ requires titolo != null;
    //@ assignable this.titolo;
    //@ ensures this.titolo == titolo;
    public void setTitolo(String titolo) {
        this.titolo = titolo;
    }

    //@ ensures \result >= 0 && \result <= 100;
    //@ pure
    public int getSconto() {
        return sconto;
    }

    //@ requires sconto >= 0 && sconto <= 100;
    //@ assignable this.sconto;
    //@ ensures this.sconto == sconto;
    public void setSconto(int sconto) {
        this.sconto = sconto;
    }

    //@ ensures \result >= 0;
    //@ pure
    public double getPrezzo() {
        return prezzo;
    }

    //@ requires prezzo >= 0;
    //@ assignable this.prezzo;
    //@ ensures this.prezzo == prezzo;
    public void setPrezzo(double prezzo) {
        this.prezzo = prezzo;
    }

    //@ ensures \result != null;
    //@ pure
    public String getIsbn() {
        return isbn;
    }

    //@ requires isbn != null;
    //@ assignable this.isbn;
    //@ ensures this.isbn == isbn;
    public void setIsbn(String isbn) {
        this.isbn = isbn;
    }

    //@ pure
    public String getGenere() {
        return genere;
    }

    //@ assignable this.genere;
    //@ ensures this.genere == genere;
    public void setGenere(String genere) {
        this.genere = genere;
    }

    //@ pure
    public String getAnnoPubblicazioni() {
        return annoPubblicazioni;
    }

    //@ assignable this.annoPubblicazioni;
    //@ ensures this.annoPubblicazioni == annoPubblicazioni;
    public void setAnnoPubblicazioni(String annoPubblicazioni) {
        this.annoPubblicazioni = annoPubblicazioni;
    }

    //@ pure
    public String getTrama() {
        return trama;
    }

    //@ assignable this.trama;
    //@ ensures this.trama == trama;
    public void setTrama(String trama) {
        this.trama = trama;
    }

    //@ pure
    public String getImmagine() {
        return immagine;
    }

    //@ assignable this.immagine;
    //@ ensures this.immagine == immagine;
    public void setImmagine(String immagine) {
        this.immagine = immagine;
    }

    //@ ensures \result != null;
    //@ pure
    public List<Autore> getAutori() {
        return autori;
    }

    //@ requires autori != null;
    //@ assignable this.autori;
    //@ ensures this.autori == autori;
    public void setAutori(List<Autore> autori) {
        this.autori = autori;
    }

    //@ also
    //@ requires isbn != null;
    //@ ensures o == null ==> !\result;
    //@ ensures \result ==> (o instanceof Libro);
    //@ ensures \result ==> this.isbn.equals(((Libro)o).isbn);
    //@ pure
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Libro libro = (Libro) o;
        return isbn.equals(libro.isbn);
        //si potrebbe fare anche solo sull'isbn
    }

    //@ pure
    public boolean isDisponibile() {
        return disponibile;
    }

    //@ assignable this.disponibile;
    //@ ensures this.disponibile == disponibile;
    public void setDisponibile(boolean disponibile) {
        this.disponibile = disponibile;
    }
}
