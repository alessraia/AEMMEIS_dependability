package model.libroService;

import model.ConPool;
import model.carrelloService.RigaCarrello;
import model.gestoreService.Gestore;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class SedeDAO {

    //@ requires sede != null;
    //@ requires sede.getCitta() != null;
    //@ requires sede.getVia() != null;
    //@ requires sede.getCivico() >= 0;
    //@ requires sede.getCap() != null;
    //@ assignable sede.idSede;
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nell'inserimento nel database *);
    public void doSave(Sede sede){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Sede (citta, via, numeroCivico, cap) VALUES(?,?,?,?)", Statement.RETURN_GENERATED_KEYS);
            ps.setString(1, sede.getCitta());
            ps.setString(2, sede.getVia());
            ps.setInt(3, sede.getCivico());
            ps.setString(4, sede.getCap());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
            ResultSet rs = ps.getGeneratedKeys();
            rs.next();
            int id = rs.getInt(1);
            sede.setIdSede(id);
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires idSede >= 0;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nella cancellazione dal database *);
    public void deleteSede(int idSede){
        try (Connection con = ConPool.getConnection()) {
            //prima cancello da appartenenza (che ha riferimenti a reparto) solo se ci sono elementi
            List<Libro> l = this.getPresenza(idSede);
            Sede s = this.doRetrieveById(idSede);
            if (l!=null && !l.isEmpty()) {
                PreparedStatement ps =
                        con.prepareStatement("DELETE FROM Presenza WHERE idSede=?");
                ps.setInt(1, idSede);
                s.setLibri(null);
                if(ps.executeUpdate() < 1)
                    throw new RuntimeException("DELETE error from appartenenza.");
            }
            //poi elimino il reparto in questione
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM sede WHERE idSede=?");
            ps.setInt(1, idSede);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires sede != null;
    //@ requires sede.getIdSede() >= 0;
    //@ requires sede.getCitta() != null;
    //@ requires sede.getVia() != null;
    //@ requires sede.getCivico() >= 0;
    //@ requires sede.getCap() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void updateSede(Sede sede){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Sede SET citta = ?, via = ?, numeroCivico = ?, cap = ? WHERE idSede = ?");
            ps.setString(1, sede.getCitta());
            ps.setString(2, sede.getVia());
            ps.setInt(3, sede.getCivico());
            ps.setString(4, sede.getCap());
            ps.setInt(5, sede.getIdSede());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    //@ requires idSede >= 0;
    //@ requires isbn != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void removeLibroSede(int idSede, String isbn){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("DELETE FROM Presenza WHERE idSede=? AND isbn = ?");
            ps.setInt(1,idSede);
            ps.setString(2, isbn);

            Sede p = this.doRetrieveById(idSede);
            LibroDAO libroService = new LibroDAO();
            Libro l = libroService.doRetrieveById(isbn);
            p.getLibri().remove(l); //ho tolto il contains perchè credo lo faccia da solo.

            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    //@ requires sede != null;
    //@ requires sede.getIdSede() >= 0;
    //@ requires isbn != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void addLibroSede(Sede sede, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Presenza (idSede, isbn) VALUES(?, ?)");
            ps.setInt(1, sede.getIdSede());
            ps.setString(2, isbn);

            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
            LibroDAO libroService = new LibroDAO();
            sede.getLibri().add(libroService.doRetrieveById(isbn));

        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public List<Sede> doRetrivedAll(){
        List<Sede> sedi = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Sede");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                Sede p = new Sede();
                p.setIdSede(rs.getInt(1));
                p.setCitta(rs.getString(2));
                p.setVia(rs.getString(3));
                p.setCivico(rs.getInt(4));
                p.setCap(rs.getString(5));
                p.setLibri(this.getPresenza(p.getIdSede()));
                sedi.add(p);
            }
            return sedi;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

    //@ requires idSede >= 0;
    //@ ensures \result == null || \result.getIdSede() == idSede;
    //@ ensures \result != null ==> \result.getCitta() != null;
    //@ ensures \result != null ==> \result.getLibri() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public Sede doRetrieveById(int idSede) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Sede WHERE idSede=?");
            ps.setInt(1, idSede);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Sede p = new Sede();
                p.setIdSede(rs.getInt(1));
                p.setCitta(rs.getString(2));
                p.setVia(rs.getString(3));
                p.setCivico(rs.getInt(4));
                p.setCap(rs.getString(5));
                p.setLibri(this.getPresenza(p.getIdSede()));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires idSede >= 0;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public List<Libro> getPresenza(int idSede){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT isbn FROM Presenza WHERE idSede=?");
            ps.setInt(1, idSede);
            List<Libro> lista=new ArrayList<>();
            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                String isbn = rs.getString(1);
                LibroDAO p = new LibroDAO();
                Libro libro=p.doRetrieveById(isbn);
                lista.add(libro);
            }
            return lista;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires idSede >= 0;
    //@ requires isbn != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void deleteFromPresenzaLibro(int idSede, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Presenza WHERE idSede=? AND isbn=?");
            ps.setInt(1, idSede);
            ps.setString(2, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires idSede >= 0;
    //@ requires isbn != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void doSavePresenza(int idSede, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Presenza (idSede, isbn) VALUES(?,?)");
            ps.setInt(1, idSede);
            ps.setString(2, isbn);
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

}
