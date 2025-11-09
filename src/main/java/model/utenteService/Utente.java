package model.utenteService;


import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.List;


/*@ nullable_by_default @*/
public class Utente {
  //@ spec_public
  private String nomeUtente;
  //@ spec_public
  private String codiceSicurezza;
  //@ spec_public
  private String email;
  //@ spec_public
  private String tipo;
  //@ spec_public
  private List<String> telefoni;


  /*@ public normal_behavior
      @   ensures \result == codiceSicurezza;
      @   assignable \nothing;
      @*/
  public /*@ pure @*/ String getCodiceSicurezza() {
    return codiceSicurezza;
  }

  /*@ public behavior
    @   requires codiceSicurezza != null && codiceSicurezza.length() > 0;
    @   assignable this.codiceSicurezza;
    @   ensures this.codiceSicurezza != null;
    @   ensures this.codiceSicurezza.length() == 40;
    @   signals (RuntimeException e) true;
    @*/
  public void setCodiceSicurezza(String codiceSicurezza) {// password è inserita dall’utente
    //this.codiceSicurezza=codiceSicurezza;
     try {
        MessageDigest digest =
                MessageDigest.getInstance("SHA-1");
        digest.reset();
        digest.update(codiceSicurezza.getBytes(StandardCharsets.UTF_8));
        this.codiceSicurezza = String.format("%040x", new
                BigInteger(1, digest.digest()));
      } catch (NoSuchAlgorithmException e) {
        throw new RuntimeException(e);

      }
  }

  /*@ public normal_behavior
      @   ensures \result == email;
      @   assignable \nothing;
      @*/
  public /*@ pure @*/ String getEmail() {
    return email;
  }

  /*@ public normal_behavior
      @   assignable this.email;
      @   ensures this.email == email;
      @*/
  public void setEmail(String email) {
    this.email = email;
  }

  /*@ public normal_behavior
      @   ensures \result == nomeUtente;
      @   assignable \nothing;
      @*/
  public /*@ pure @*/ String getNomeUtente() {
    return nomeUtente;
  }

  /*@ public normal_behavior
      @   assignable this.nomeUtente;
      @   ensures this.nomeUtente == nomeUtente;
      @*/
  public void setNomeUtente(String nomeUtente) {
    this.nomeUtente = nomeUtente;
  }

  /*@ public normal_behavior
      @   ensures \result == tipo;
      @   assignable \nothing;
      @*/
  public /*@ pure @*/ String getTipo() {
    return tipo;
  }

  /*@ public normal_behavior
      @   assignable this.tipo;
      @   ensures this.tipo == tipo;
      @*/
  public void setTipo(String tipo) {
    this.tipo = tipo;
  }

  /*@ public normal_behavior
      @   ensures \result == telefoni;
      @   assignable \nothing;
      @*/
  public /*@ pure @*/ List<String> getTelefoni() {
    return telefoni;
  }

  /*@ public normal_behavior
      @ requires telefoni == null
      @     || (\forall int i; 0 <= i && i < telefoni.size(); telefoni.get(i) != null);
      @ assignable this.telefoni;
      @ ensures this.telefoni == telefoni;
     */
  public void setTelefoni(List<String> telefoni) {
    this.telefoni = telefoni;
  }
}
