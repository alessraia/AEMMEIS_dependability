package model.carrelloService;

import model.ConPool;
import model.gestoreService.Gestore;
import model.tesseraService.Tessera;
import model.utenteService.Utente;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

public class CarrelloDAO {

    /*@
     @ public behavior
     @ requires carrello != null;
     @ assignable \nothing;
     @ requires carrello.getIdCarrello() != null && !carrello.getIdCarrello().isEmpty();
     @ requires carrello.getEmail() != null && !carrello.getEmail().isEmpty();
     @ requires carrello.getTotale() >= 0;
     @ signals_only RuntimeException;
    @*/
    public void doSave(Carrello carrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO carrello (idCarrello, totale, email) VALUES(?,?,?)");
            ps.setString(1, carrello.getIdCarrello());
            ps.setDouble(2, carrello.getTotale());
            ps.setString(3, carrello.getEmail());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
     @ public behavior
     @ requires idCarrello != null && !idCarrello.isEmpty();
     @ assignment \nothing;
     @ signals_only RuntimeException;
    @*/
    public void deleteCarrello(String idCarrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM carrello WHERE idCarrello=?");
            ps.setString(1, idCarrello);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
     @ public behavior
     @ assignable \nothing;
     @ requires carrello != null;
     @ requires carrello.getIdCarrello() != null && !carrello.getIdCarrello().isEmpty();
     @ requires carrello.getTotale() >= 0;
     @ signals_only RuntimeException;
    @*/
    public void updateCarrello(Carrello carrello){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE carrello SET totale = ? WHERE idCarrello = ?");
            ps.setDouble(1, carrello.getTotale());
            ps.setString(2, carrello.getIdCarrello());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    /*@
     @ public behavior
     @ assignable \nothing;
     @ requires idCarrello != null && !idCarrello.isEmpty();
     @ ensures \result == null
     @          || (\result.getIdCarrello() != null && !\result.getIdCarrello().isEmpty()
     @          && \result.getEmail() != null && !\result.getEmail().isEmpty()
     @          && \result.getTotale() >= 0
     @          && \result.getRigheCarrello != null
     @ );
     @ signals_only RuntimeException;
    @*/
    public Carrello doRetriveById(String idCarrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM carrello WHERE idCarrello=?");
            ps.setString(1, idCarrello);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Carrello carrello = new Carrello();
                RigaCarrelloDAO rigaService = new RigaCarrelloDAO();
                carrello.setIdCarrello(idCarrello);
                carrello.setTotale(rs.getDouble(2));
                carrello.setEmail(rs.getString(3));
                carrello.setRigheCarrello(rigaService.doRetrieveByIdCarrello(idCarrello));
                return carrello;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
     @ public behavior
     @ assignable \nothing;
     @ requires email != null && !email.isEmpty();
     @ ensures \result == null
     @          || (\result.getIdCarrello() != null && !\result.getIdCarrello().isEmpty()
     @          && \result.getEmail() != null && !\result.getEmail().isEmpty()
     @          && \result.getTotale() >= 0
     @          && \result.getRigheCarrello != null
     @ );
     @ signals_only RuntimeException;
    @*/
    public Carrello doRetriveByUtente(String email){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM carrello WHERE email=?");
            ps.setString(1, email);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Carrello carrello = new Carrello();
                RigaCarrelloDAO rigaService = new RigaCarrelloDAO();
                carrello.setIdCarrello(rs.getString(1));
                carrello.setTotale(rs.getDouble(2));
                carrello.setEmail(rs.getString(3));
                carrello.setRigheCarrello(rigaService.doRetrieveByIdCarrello(carrello.getIdCarrello()));
                return carrello;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
     @ public behavior
     @ ensures \result != null;
     @ assignable \nothing;
     @ ensures (\forall int i; 0 <= i && i < \result.size();
     @              \result.get(i) != null && !\result.get(i).isEmpty()
     @ );
     @ signals_only RuntimeException;
    @*/
    public List<String> doRetrivedAllIdCarrelli(){
        List<String>  idCarrello = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM carrello");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                idCarrello.add(rs.getString(1));
            }
            return idCarrello;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }
}
