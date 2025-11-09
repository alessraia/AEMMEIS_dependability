package model.tesseraService;
import java.time.LocalDate;

/*@ nullable_by_default @*/
public class Tessera {
    //@ spec_public
    private String numero;
    //@ spec_public
    private LocalDate dataCreazione;
    //@ spec_public
    private LocalDate dataScadenza;
    //@ spec_public
    private int punti;
    //@ spec_public
    private String email;

    /*@
      @ public normal_behavior
      @   ensures \result == this.numero;
      @   assignable \nothing;
      @*/
    public String getNumero() {
        return numero;
    }

    /*@
      @ public normal_behavior
      @   requires numero != null && !numero.isEmpty();
      @   assignable this.numero;
      @   ensures this.numero == numero;
      @*/
    public void setNumero(String numero) {
        this.numero = numero;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.dataCreazione;
      @   assignable \nothing;
      @*/
    public LocalDate getDataCreazione() {
        return dataCreazione;
    }

    /*@
      @ public normal_behavior
      @   requires dataCreazione != null;
      @   assignable this.dataCreazione;
      @   ensures this.dataCreazione == dataCreazione;
      @*/
    public void setDataCreazione(LocalDate dataCreazione) {
        this.dataCreazione = dataCreazione;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.dataScadenza;
      @   assignable \nothing;
      @*/
    public LocalDate getDataScadenza() {
        return dataScadenza;
    }

    /*@
      @ public normal_behavior
      @   requires dataScadenza != null;
      @   assignable this.dataScadenza;
      @   ensures this.dataScadenza == dataScadenza;
      @*/
    public void setDataScadenza(LocalDate dataScadenza) {
        this.dataScadenza = dataScadenza;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.punti;
      @   assignable \nothing;
      @*/
    public int getPunti() {
        return punti;
    }

    /*@
      @ public normal_behavior
      @   requires punti >= 0;
      @   assignable this.punti;
      @   ensures this.punti == punti;
      @*/
    public void setPunti(int punti) {
        this.punti = punti;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.email;
      @   assignable \nothing;
      @*/
    public String getEmail() {
        return email;
    }

    /*@
      @ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable this.email;
      @   ensures this.email == email;
      @*/
    public void setEmail(String email) {
        this.email = email;
    }
}
