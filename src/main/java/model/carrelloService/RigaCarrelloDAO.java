package model.carrelloService;

import model.ConPool;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

public class RigaCarrelloDAO {


    /*@
     @ public behavior
     @ requires idCarrello != null && !idCarrello.isEmpty();
     @ ensures \result != null;
     @ assignable \nothing;
     @ ensures (\forall int i; 0 <= i && i <= \result.size(); \result.get(i) != null && \result.get(i).getIdCarrello() != null && !\result.get(i).getIdCarrello().isEmpty() && \result.get(i).getIdCarrello().equals(idCarrello) && \result.get(i).getQuantita() >= 0 && \result.get(i).getLibro() != null);
     @ signals_only RuntimeException;
    @*/
    public List<RigaCarrello> doRetrieveByIdCarrello(String idCarrello) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM rigacarrello WHERE idCarrello=?");
            ps.setString(1, idCarrello);
            ResultSet rs = ps.executeQuery();
            List<RigaCarrello> lista = new ArrayList<>();
            while (rs.next()) {
                RigaCarrello p = new RigaCarrello();
                LibroDAO libroService= new LibroDAO();
                p.setIdCarrello(rs.getString(1));
                String isbn=rs.getString(2);
                p.setLibro(libroService.doRetrieveById(isbn));
                //p.setIsbn(rs.getString(2));
                p.setQuantita(rs.getInt(3));
                lista.add(p);
            }
            return lista;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
    @ public behavior
    @ requires idCarrello != null && !idCarrello.isEmpty();
    @ requires isbn != null && !isbn.isEmpty();
    @ assignable \nothing;
    @ ensures \result == null ||  \result!= null && \result.getIdCarrello() != null && !\result.getIdCarrello().isEmpty() && \result.getIdCarrello().equals(idCarrello) && \result.getQuantita() >= 0 && \result.getLibro() != null;
    @ signals_only RuntimeException;
   @*/
    public RigaCarrello doRetriveById(String idCarrello, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM rigacarrello WHERE idCarrello=? AND isbn=?");
            ps.setString(1, idCarrello);
            ps.setString(2, isbn);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                RigaCarrello p = new RigaCarrello();
                LibroDAO libroService= new LibroDAO();
                p.setIdCarrello(rs.getString(1));
                p.setLibro(libroService.doRetrieveById(isbn));
                //p.setIsbn(rs.getString(2));
                p.setQuantita(rs.getInt(3));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
    @ public behavior
    @ requires rigaCarrello != null;
    @ assignable \nothing;
    @ requires rigaCarrello.getIdCarrello() != null && !rigaCarrello.getIdCarrello().isEmpty();
    @ requires rigaCarrello.getLibro() != null;
    @ requires rigaCarrello.getQuantita() >= 0;
    @ signals_only RuntimeException;
   @*/
    public void doSave(RigaCarrello rigaCarrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO rigacarrello (idCarrello, isbn, quantita) VALUES(?,?,?)");
            ps.setString(1, rigaCarrello.getIdCarrello());
            ps.setString(2, rigaCarrello.getLibro().getIsbn());
            ps.setInt(3, rigaCarrello.getQuantita());
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
    @ requires isbn != null && !isbn.isEmpty();
    @ assignable \nothing;
    @ signals_only RuntimeException;
   @*/
    public void deleteRigaCarrello(String isbn, String idCarrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM rigacarrello WHERE idCarrello=? AND isbn =?");
            ps.setString(1, idCarrello);
            ps.setString(2, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
    @ public behavior
    @ requires idCarrello != null && !idCarrello.isEmpty();
    @ assignable \nothing;
    @ signals_only RuntimeException;
   @*/
    public void deleteRigheCarrelloByIdCarrello(String idCarrello){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM rigacarrello WHERE idCarrello=?");
            ps.setString(1, idCarrello);
            if(ps.executeUpdate() < 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@
    @ public behavior
    @ requires rigaCarrello != null;
    @ assignable \nothing;
    @ requires rigaCarrello.getIdCarrello() != null && !rigaCarrello.getIdCarrello().isEmpty();
    @ requires rigaCarrello.getLibro() != null;
    @ requires rigaCarrello.getQuantita() >= 0;
    @ signals_only RuntimeException;
   @*/
    public void updateQuantita(RigaCarrello rigaCarrello){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE rigaCarrello SET quantita = ? WHERE isbn = ? AND idCarrello=?");
            ps.setInt(1,rigaCarrello.getQuantita());
            ps.setString(2, rigaCarrello.getLibro().getIsbn());
            ps.setString(3, rigaCarrello.getIdCarrello());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }
}
