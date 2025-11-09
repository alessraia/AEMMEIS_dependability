package model.ordineService;

import model.ConPool;
import model.carrelloService.RigaCarrello;
import model.libroService.LibroDAO;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

public class RigaOrdineDAO {

    /*@ public behavior
      @ requires rigaOrdine != null;
      @ requires rigaOrdine.getIdOrdine() != null && rigaOrdine.getIdOrdine().length() > 0;
      @ requires rigaOrdine.getIsbn() != null && rigaOrdine.getIsbn().length() > 0;
      @ requires rigaOrdine.getPrezzoUnitario() != null && rigaOrdine.getPrezzoUnitario() >= 0.0;
      @ requires rigaOrdine.getQuantita() != null && rigaOrdine.getQuantita() >= 1;
      @ assignable \nothing;
      @ ensures true;
      @ signals (RuntimeException e) true;
      @*/
    public void doSave(RigaOrdine rigaOrdine){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO rigaordine (idOrdine, isbn, prezzoUnitario, quantita) VALUES(?,?,?, ?)");
            ps.setString(1, rigaOrdine.getIdOrdine());
            ps.setString(2, rigaOrdine.getLibro().getIsbn());
            ps.setDouble(3, rigaOrdine.getPrezzoUnitario());
            ps.setInt(4, rigaOrdine.getQuantita());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
  @   requires idOrdine != null && idOrdine.length() > 0;
  @   assignable \nothing;
  @   ensures \result != null;
  @   ensures (\forall int i; 0 <= i && i < \result.size();
  @              \result.get(i) != null
  @           && idOrdine.equals(\result.get(i).getIdOrdine())
  @           && \result.get(i).getPrezzoUnitario() >= 0.0
  @           && \result.get(i).getQuantita() >= 1);
  @   signals (RuntimeException e) true;
  @*/
    public List<RigaOrdine> doRetrivedByOrdine(String idOrdine) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM rigaordine WHERE idOrdine=?");
            ps.setString(1, idOrdine);
            ResultSet rs = ps.executeQuery();
            List<RigaOrdine> lista = new ArrayList<>();
            while (rs.next()) {
                RigaOrdine p = new RigaOrdine();
                LibroDAO libroService= new LibroDAO();
                p.setIdOrdine(rs.getString(1));
                String isbn=rs.getString(2);
                p.setLibro(libroService.doRetrieveById(isbn));
                //p.setIsbn(rs.getString(2));
                p.setPrezzoUnitario(rs.getDouble(3));
                p.setQuantita(rs.getInt(4));
                lista.add(p);
            }
            return lista;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
  @   requires idOrdine != null && idOrdine.length() > 0;
  @   requires isbn != null && isbn.length() > 0;
  @   assignable \nothing;
  @   ensures \result == null
  @        || ( \result.getIdOrdine() != null
  @          && \result.getIdOrdine().equals(idOrdine)
  @          && \result.getLibro() != null
  @          && \result.getLibro().getIsbn().equals(isbn)
  @          && \result.getPrezzoUnitario() >= 0.0
  @          && \result.getQuantita() >= 1 );
  @   signals (RuntimeException e) true;
  @*/
    public RigaOrdine doRetriveById(String idOrdine, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM rigaordine WHERE idOrdine=? AND isbn=?");
            ps.setString(1, idOrdine);
            ps.setString(2, isbn);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                RigaOrdine p = new RigaOrdine();
                LibroDAO libroService= new LibroDAO();
                p.setIdOrdine(rs.getString(1));
                p.setLibro(libroService.doRetrieveById(isbn));
                //p.setIsbn(rs.getString(2));
                p.setPrezzoUnitario(rs.getDouble(3));
                p.setQuantita(rs.getInt(4));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }
    /*@ public behavior
    @   requires isbn != null && isbn.length() > 0;
    @   requires idOrdine != null && idOrdine.length() > 0;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    public void deleteRigaOrdine(String isbn, String idOrdine){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM rigaordine WHERE idOrdine=? AND isbn =?");
            ps.setString(1, idOrdine);
            ps.setString(2, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
    @   requires idOrdine != null && idOrdine.length() > 0;
    @   assignable \nothing;
    @   ensures true;
    @   signals (RuntimeException e) true;
    @*/
    public void deleteRigaOrdineByIdOrdine(String idOrdine){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM rigaordine WHERE idOrdine=?");
            ps.setString(1, idOrdine);
            if(ps.executeUpdate() < 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

}
