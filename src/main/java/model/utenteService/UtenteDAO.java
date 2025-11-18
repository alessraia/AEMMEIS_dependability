package model.utenteService;

import model.ConPool;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrelloDAO;
import model.ordineService.OrdineDAO;
import model.tesseraService.TesseraDAO;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;


public class UtenteDAO {
    /*@ public behavior
      @   requires email != null && email.length() > 0;
      @   assignable \nothing;
      @   ensures \result == null
      @        || (\result.getEmail() != null && \result.getEmail().equals(email) && \result.getNomeUtente() != null && \result.getCodiceSicurezza() != null && \result.getTipo() != null && \result.getTelefoni() != null);
      @   signals (RuntimeException e) true;
      @*/
    public Utente doRetrieveById(String email) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT nomeUtente, email, codiceSicurezza, tipo FROM Utente WHERE email=?");
            ps.setString(1, email);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Utente p = new Utente();
                p.setNomeUtente(rs.getString(1));
                p.setEmail(rs.getString(2));
                p.setCodiceSicurezza(rs.getString(3));
                p.setTipo(rs.getString(4));
                p.setTelefoni(this.cercaTelefoni(p.getEmail()));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
     @   requires email != null && email.length() > 0
     @         && password != null && password.length() > 0;
     @   assignable \nothing;
     @   ensures \result == null
     @        || (\result.getEmail() != null
     @            && \result.getEmail().equals(email) && \result.getNomeUtente() != null
     @            && \result.getCodiceSicurezza() != null && \result.getTipo() != null && \result.getTelefoni() != null);
     @   signals (RuntimeException e) true;
     @*/
    public Utente doRetrieveByEmailPassword(String email, String password) {
        try (Connection con = ConPool.getConnection()) {

            PreparedStatement ps =
                    con.prepareStatement("SELECT nomeUtente, email, codiceSicurezza, tipo FROM Utente WHERE email=? AND  codiceSicurezza=?");//SHA1(?)
            ps.setString(1, email);
            ps.setString(2, password);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Utente p = new Utente();
                p.setNomeUtente(rs.getString(1));
                p.setEmail(rs.getString(2));
                p.setCodiceSicurezza(rs.getString(3));
                p.setTipo(rs.getString(4));
                p.setTelefoni(this.cercaTelefoni(p.getEmail()));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }


    /*@ public behavior
      @   requires utente != null
      @        && utente.getEmail() != null
      @        && utente.getEmail().length() > 0
      @        && utente.getNomeUtente() != null
      @        && utente.getEmail() != null && utente.getEmail().length() > 0
      @        && utente.getCodiceSicurezza() != null && utente.getCodiceSicurezza().length() > 0
      @        && utente.getTipo() != null && utente.getTipo().length() > 0
      @        && utente.getTelefoni() != null;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void doSave(Utente utente) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Utente (nomeUtente, email, codiceSicurezza, tipo) VALUES(?,?,?,?)");
            ps.setString(1, utente.getNomeUtente());
            ps.setString(2, utente.getEmail());
            ps.setString(3, utente.getCodiceSicurezza());
            ps.setString(4, utente.getTipo());

            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }

            for(String tel : utente.getTelefoni()){
                this.addTelefono(utente.getEmail(), tel);
            }

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    /*@ public behavior
  @   assignable \nothing;
  @   ensures \result != null;
  @   ensures (\forall int i; 0 <= i && i < \result.size();
  @              \result.get(i) != null
  @           && \result.get(i).getEmail() != null
  @           && \result.get(i).getEmail().length() > 0
  @           && \result.get(i).getNomeUtente() != null
  @           && \result.get(i).getCodiceSicurezza() != null
  @           && \result.get(i).getCodiceSicurezza().length() > 0
  @           && \result.get(i).getTipo() != null
  @           && \result.get(i).getTipo().length() > 0);
  @   signals (RuntimeException e) true;
  @*/
    public List<Utente> doRetrieveAll() {
        List<Utente> utenti = new ArrayList<Utente>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Utente");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                Utente p = new Utente();
                p.setNomeUtente(rs.getString(1));
                p.setEmail(rs.getString(2));
                p.setCodiceSicurezza(rs.getString(3));
                p.setTipo(rs.getString(4));
                utenti.add(p);
            }
            return utenti;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
     @   requires utente != null
      @        && utente.getEmail() != null
      @        && utente.getEmail().length() > 0
      @        && utente.getNomeUtente() != null
      @        && utente.getEmail() != null && utente.getEmail().length() > 0
      @        && utente.getCodiceSicurezza() != null && utente.getCodiceSicurezza().length() > 0
      @        && utente.getTipo() != null && utente.getTipo().length() > 0
      @        && utente.getTelefoni() != null;
     @   assignable \nothing;
     @   signals (RuntimeException e) true;
     @*/
    public void updateUtente(Utente utente){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Utente SET nomeUtente = ?, tipo = ? WHERE email = ?");
            ps.setString(1, utente.getNomeUtente());
            ps.setString(2, utente.getTipo());
            ps.setString(3, utente.getEmail());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
            List<String> telefoni = this.cercaTelefoni(utente.getEmail());
            for (String tel : utente.getTelefoni() ){
                if(!(telefoni.contains(tel))){
                    this.addTelefono(utente.getEmail(), tel);
                }
            }
            for (String tel : telefoni ){
                if(!(utente.getTelefoni().contains(tel))){
                    this.deleteTelefono(utente.getEmail(), tel);
                }
            }

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires utente != null
      @        && utente.getEmail() != null
      @        && utente.getEmail().length() > 0
      @        && utente.getCodiceSicurezza() != null && utente.getCodiceSicurezza().length() > 0;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void updateUtentePassword(Utente utente){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Utente SET codiceSicurezza = ? WHERE email = ?");
            ps.setString(1, utente.getCodiceSicurezza());
            ps.setString(2, utente.getEmail());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void deleteUtente(String email){

        if(this.doRetrieveById(email).getTipo().equalsIgnoreCase("premium")){
            TesseraDAO tesseraDAO = new TesseraDAO();
            tesseraDAO.deleteTessera(tesseraDAO.doRetrieveByEmail(email).getNumero()); //cancello eventuale tessera
        }
        if(!this.doRetrieveById(email).getTelefoni().isEmpty())
            this.deleteTelefoni(email); //relazione con telefoni

        RigaCarrelloDAO rigaCarrelloDAO = new RigaCarrelloDAO();
        CarrelloDAO carrelloDAO = new CarrelloDAO();
        OrdineDAO ordineDAO = new OrdineDAO();
        if(!ordineDAO.doRetrieveByUtente(email).isEmpty())
            ordineDAO.deleteOrdiniByEmail(email);
        Carrello carrello = carrelloDAO.doRetriveByUtente(email);
        if(!rigaCarrelloDAO.doRetrieveByIdCarrello(carrello.getIdCarrello()).isEmpty())
            rigaCarrelloDAO.deleteRigheCarrelloByIdCarrello(carrello.getIdCarrello());
        carrelloDAO.deleteCarrello(carrello.getIdCarrello());


        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Utente WHERE email=?");
            ps.setString(1, email);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0
      @        && numeroTelefono != null && numeroTelefono.length() > 0;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void deleteTelefono(String email, String numeroTelefono){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Telefono WHERE email=? AND numeroTelefono=?");
            ps.setString(1, email);
            ps.setString(2, numeroTelefono);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void deleteTelefoni(String email){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Telefono WHERE email=?");//Per farlo funzionare bisogna togliere la safe mode dal db
            ps.setString(1, email);
            if(ps.executeUpdate() < 1)
                throw new RuntimeException("DELETE error. Email: " + email + " not present in the db");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0
      @        && numeroTelefono != null && numeroTelefono.length() == 10;
      @   assignable \nothing;
      @   signals (RuntimeException e) true;
      @*/
    public void addTelefono(String email, String numeroTelefono){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Telefono (numeroTelefono, email) VALUES(?,?)");
            ps.setString(1, numeroTelefono);
            ps.setString(2, email);
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }


//mi serve una funzione che cerchi i numeri di telefono di un utente e li salvi nella lista
//così da non perdere l'informazione quando si fa il login.

    /*@ public behavior
  @   requires email != null && email.length() > 0;
  @   assignable \nothing;
  @   ensures \result != null;
  @   ensures (\forall int i; 0 <= i && i < \result.size();
  @              \result.get(i) != null
  @           && \result.get(i).length() == 10);
  @   signals (RuntimeException e) true;
  @*/
    public List<String> cercaTelefoni(String email) {
        List<String> telefoni = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT numeroTelefono FROM Telefono WHERE email=?");
            ps.setString(1, email);
            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                telefoni.add(rs.getString(1));
            }
            return telefoni;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures (\forall int i; 0 <= i && i < \result.size();
      @               \result.get(i) != null && \result.get(i).length() == 10);
      @   signals (RuntimeException e) true;
      @*/
    public List<String> doRetrieveAllTelefoni() {
        List<String> telefoni = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT numeroTelefono FROM Telefono");
            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
               telefoni.add(rs.getString(1));
            }
            return telefoni;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }
}