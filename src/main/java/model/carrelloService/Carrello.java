package model.carrelloService;

import java.util.List;
/*@ nullable_by_default @*/
public class Carrello {
    //@ spec_public
    private String idCarrello;
    //@ spec_public
    private double totale;
    //@ spec_public
    private String email;
    //@ spec_public
    private List<RigaCarrello> righeCarrello;

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
      @   ensures \result == this.totale;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ double getTotale() {
        return totale;
    }

    /*@
      @ public normal_behavior
      @   requires totale >= 0;
      @   assignable this.totale;
      @   ensures this.totale == totale;
      @*/
    public void setTotale(double totale) {
        this.totale = totale;
    }

    /*@
      @ public normal_behavior
      @   ensures \result == this.email;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ String getEmail() {
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

    /*@
      @ public normal_behavior
      @   ensures \result == this.righeCarrello;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ List<RigaCarrello> getRigheCarrello() {
        return righeCarrello;
    }

    /*@
      @ public normal_behavior
      @   requires righeCarrello != null;
      @   requires (\forall int i; 0 <= i && i < righeCarrello.size();
      @               righeCarrello.get(i) != null);
      @   assignable this.righeCarrello;
      @   ensures this.righeCarrello == righeCarrello;
    @*/
    public void setRigheCarrello(List<RigaCarrello> righeCarrello) {
        this.righeCarrello = righeCarrello;
    }
}
