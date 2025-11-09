package model.ordineService;

import java.time.LocalDate;
import java.util.Date;
import java.util.List;

/*@ nullable_by_default @*/
public class Ordine {
    //@ spec_public
    private String idOrdine;
    //@ spec_public
    private double costo;
    //@ public invariant costo >= 0.0;

    //@ spec_public
    private String indirizzoSpedizione;
    //@ spec_public
    private String citta;
    //@ spec_public
    private int puntiOttenuti;
    //@ public invariant puntiOttenuti >= 0;

    //@ spec_public
    private int puntiSpesi;
    //@ public invariant puntiSpesi >= 0;

    //@ spec_public
    private LocalDate dataArrivo;
    //@ spec_public
    private LocalDate dataEffettuazione;
    //@ spec_public
    private String stato;
    //@ spec_public
    private String matricola;
    //@ spec_public
    private String email;
    //aggiunto questo
    //@ spec_public
    private List<RigaOrdine> righeOrdine;
    //@ public invariant righeOrdine == null
    //@        || (\forall int i; 0 <= i && i < righeOrdine.size(); righeOrdine.get(i) != null);


    /*@ public normal_behavior
      @   ensures \result == citta;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getCitta() {
        return citta;
    }

    /*@ public normal_behavior
      @ assignable this.citta;
      @ ensures this.citta == citta;
     */
    public void setCitta(String citta) {
        this.citta = citta;
    }

    /*@ public normal_behavior
      @   ensures \result == costo;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/double getCosto() {
        return costo;
    }

    /*@ public normal_behavior
      @ requires costo >= 0.0;
      @ assignable this.costo;
      @ ensures this.costo == costo;
     */
    public void setCosto(double costo) {
        this.costo = costo;
    }

    /*@ public normal_behavior
      @   ensures \result == dataArrivo;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ LocalDate getDataArrivo() {
        return dataArrivo;
    }

    /*@ public normal_behavior
      @ requires dataArrivo!= null && !dataArrivo.isBefore(this.dataEffettuazione);
      @ assignable this.dataArrivo;
      @ ensures this.dataArrivo == dataArrivo;
     */
    public void setDataArrivo(LocalDate dataArrivo) {
        this.dataArrivo = dataArrivo;
    }

    /*@ public normal_behavior
      @   ensures \result == dataEffettuazione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ LocalDate getDataEffettuazione() {
        return dataEffettuazione;
    }

   /*@ public normal_behavior
     @ requires this.dataArrivo == null
     @       || dataEffettuazione == null
     @       || !this.dataArrivo.isBefore(dataEffettuazione);
     @ assignable this.dataEffettuazione;
     @ ensures this.dataEffettuazione == dataEffettuazione;
     @*/
    public void setDataEffettuazione(LocalDate dataEffettuazione) {
        this.dataEffettuazione = dataEffettuazione;
    }

    /*@ public normal_behavior
      @   ensures \result == idOrdine;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getIdOrdine() {
        return idOrdine;
    }

    /*@ public normal_behavior
      @ assignable this.idOrdine;
      @ ensures this.idOrdine == idOrdine;
     */
    public void setIdOrdine(String idOrdine) {
        this.idOrdine = idOrdine;
    }

    /*@ public normal_behavior
      @   ensures \result == indirizzoSpedizione;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getIndirizzoSpedizione() {
        return indirizzoSpedizione;
    }

    /*@ public normal_behavior
      @ assignable this.indirizzoSpedizione;
      @ ensures this.indirizzoSpedizione == indirizzoSpedizione;
     */
    public void setIndirizzoSpedizione(String indirizzoSpedizione) {
        this.indirizzoSpedizione = indirizzoSpedizione;
    }

    /*@ public normal_behavior
      @   ensures \result == puntiOttenuti;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getPuntiOttenuti() {
        return puntiOttenuti;
    }

    /*@ public normal_behavior
      @ requires puntiOttenuti >= 0;
      @ assignable this.puntiOttenuti;
      @ ensures this.puntiOttenuti == puntiOttenuti;
     */
    public void setPuntiOttenuti(int puntiOttenuti) {
        this.puntiOttenuti = puntiOttenuti;
    }

    /*@ public normal_behavior
      @   ensures \result == puntiSpesi;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getPuntiSpesi() {
        return puntiSpesi;
    }

    /*@ public normal_behavior
      @ requires puntiSpesi >= 0;
      @ assignable this.puntiSpesi;
      @ ensures this.puntiSpesi == puntiSpesi;
     */
    public void setPuntiSpesi(int puntiSpesi) {
        this.puntiSpesi = puntiSpesi;
    }

    /*@ public normal_behavior
      @   ensures \result == stato;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getStato() {
        return stato;
    }

    /*@ public normal_behavior
      @ assignable this.stato;
      @ ensures this.stato == stato;
     */
    public void setStato(String stato) {
        this.stato = stato;
    }

    /*@ public normal_behavior
      @   ensures \result == email;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getEmail() {
        return email;
    }

    /*@ public normal_behavior
      @ assignable this.email;
      @ ensures this.email == email;
     */
    public void setEmail(String email) {
        this.email = email;
    }

    /*@ public normal_behavior
      @   ensures \result == matricola;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getMatricola() {
        return matricola;
    }

    /*@ public normal_behavior
      @ assignable this.matricola;
      @ ensures this.matricola == matricola;
     */
    public void setMatricola(String matricola) {
        this.matricola = matricola;
    }

    /*@ public normal_behavior
      @   ensures \result == righeOrdine;
      @   assignable \nothing;
      @*/
    //aggiunto questi
    public /*@ pure @*/ List<RigaOrdine> getRigheOrdine() {
        return righeOrdine;
    }

    /*@ public normal_behavior
      @ requires righeOrdine == null
      @     || (\forall int i; 0 <= i && i < righeOrdine.size(); righeOrdine.get(i) != null);
      @ assignable this.righeOrdine;
      @ ensures this.righeOrdine == righeOrdine;
     */
    public void setRigheOrdine(List<RigaOrdine> righeOrdine) {
        this.righeOrdine = righeOrdine;
    }
}
