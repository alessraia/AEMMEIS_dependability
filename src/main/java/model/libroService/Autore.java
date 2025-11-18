package model.libroService;
/*@ nullable_by_default @*/
public class Autore {
    //@ spec_public
    private String cf;

    //@ spec_public
    private String nome;

    //@ spec_public
    private String cognome;

    //@ ensures \result != null;
    //@ pure
    public String getCf() {
        return cf;
    }

    //@ requires cf != null;
    //@ assignable this.cf;
    //@ ensures this.cf == cf;
    public void setCf(String cf) {
        this.cf = cf;
    }

    //@ ensures \result != null;
    //@ pure
    public String getCognome() {
        return cognome;
    }

    //@ requires cognome != null;
    //@ assignable this.cognome;
    //@ ensures this.cognome == cognome;
    public void setCognome(String cognome) {
        this.cognome = cognome;
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
}
