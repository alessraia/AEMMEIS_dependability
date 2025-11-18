package model.libroService;
import model.ConPool;
import model.utenteService.Utente;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class AutoreDAO {


    //@ requires autore != null;
    //@ requires autore.getCf() != null;
    //@ requires autore.getNome() != null;
    //@ requires autore.getCognome() != null;
    //@ assignable \nothing; // Modifica solo il database, non lo stato dell'oggetto
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nell'inserimento nel database *);
    public void doSave(Autore autore){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Autore (cf, nome, cognome) VALUES(?,?,?)",
                    Statement.RETURN_GENERATED_KEYS);
            ps.setString(1, autore.getCf());
            ps.setString(2, autore.getNome());
            ps.setString(3, autore.getCognome());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }


    //@ requires cf != null;
    //@ assignable \nothing; // Modifica solo il database
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nella cancellazione dal database *);
    public void deleteAutore(String cf){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Autore WHERE cf=?");
            ps.setString(1, cf);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }


    //@ requires cf != null;
    //@ ensures \result == null || \result.getCf().equals(cf);
    //@ ensures \result != null ==> \result.getNome() != null;
    //@ ensures \result != null ==> \result.getCognome() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public Autore searchAutore(String cf) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT nome, cognome FROM Autore WHERE cf=?");
            ps.setString(1, cf);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Autore autore = new Autore();
                autore.setCf(cf);
                autore.setNome(rs.getString(1));
                autore.setCognome(rs.getString(2));
                return autore;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }


    //@ requires cf != null;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).getIsbn() != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public List<Libro> getScrittura(String cf){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT isbn FROM Scrittura WHERE cf=?");
            ps.setString(1, cf);
            List<Libro> lista = new ArrayList<Libro>();
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


}
