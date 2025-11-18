package model.libroService;
import model.ConPool;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class LibroDAO {

    //@ requires libro != null;
    //@ requires libro.getIsbn() != null;
    //@ requires libro.getTitolo() != null;
    //@ requires libro.getPrezzo() >= 0;
    //@ requires libro.getSconto() >= 0 && libro.getSconto() <= 100;
    //@ requires libro.getAutori() != null;
    //@ assignable \nothing; // Modifica solo il database
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nell'inserimento nel database *);
    public void doSave(Libro libro){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Libro (isbn, titolo, genere, annoPubblicazione, prezzo, sconto, trama, immagine) VALUES(?,?,?,?,?,?,?,?)");
            ps.setString(1, libro.getIsbn());
            ps.setString(2, libro.getTitolo());
            ps.setString(3, libro.getGenere());
            ps.setString(4, libro.getAnnoPubblicazioni());
            ps.setDouble(5, libro.getPrezzo());
            ps.setInt(6, libro.getSconto());
            ps.setString(7, libro.getTrama());
            ps.setString(8, libro.getImmagine());
            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }

            for(Autore autore : libro.getAutori()){
                this.addAutore(libro.getIsbn(), autore);
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ assignable \nothing; // Modifica solo il database
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nella cancellazione dal database *);
    public void deleteLibro(String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Rigacarrello WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE1 error.");

            ps = con.prepareStatement("DELETE FROM Wishlist WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE2 error.");

            ps = con.prepareStatement("DELETE FROM Reparto WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE3 error.");

            ps = con.prepareStatement("DELETE FROM Sede WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE4 error.");

            ps = con.prepareStatement("DELETE FROM Scrittura WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE4 error.");

            ps = con.prepareStatement("DELETE FROM Libro WHERE isbn=?");
            ps.setString(1, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE5 error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires libro != null;
    //@ requires libro.getIsbn() != null;
    //@ requires libro.getSconto() >= 0 && libro.getSconto() <= 100;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void updateLibroSconto(Libro libro){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Libro SET sconto = ? WHERE isbn = ?");
            ps.setInt(1, libro.getSconto());
            ps.setString(2, libro.getIsbn());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }

    }

    //@ requires libro != null;
    //@ requires libro.getIsbn() != null;
    //@ requires libro.getTitolo() != null;
    //@ requires libro.getPrezzo() >= 0;
    //@ requires libro.getSconto() >= 0 && libro.getSconto() <= 100;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void updateLibro(Libro libro){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Libro SET titolo = ?, genere = ?, " +
                    "annoPubblicazione = ?, prezzo = ?, sconto = ?, trama = ?, immagine = ? WHERE isbn = ?");
            ps.setString(1, libro.getTitolo());
            ps.setString(2, libro.getGenere());
            ps.setString(3, libro.getAnnoPubblicazioni());
            ps.setDouble(4, libro.getPrezzo());
            ps.setInt(5, libro.getSconto());
            ps.setString(6, libro.getTrama());
            ps.setString(7, libro.getImmagine());
            ps.setString(8, libro.getIsbn());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires libro != null;
    //@ requires libro.getIsbn() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void updateDisponibile(Libro libro){
        try(Connection con = ConPool.getConnection()){
            PreparedStatement ps = con.prepareStatement("UPDATE Libro SET disponibile = ? WHERE isbn = ?");
            ps.setBoolean(1, libro.isDisponibile());
            ps.setString(2, libro.getIsbn());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("UPDATE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).getIsbn() != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public List<Libro> doRetriveAll(){
        List<Libro> libri = new ArrayList<>();
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Libro");

            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                Libro p = new Libro();
                p.setIsbn(rs.getString(1));
                p.setTitolo(rs.getString(2));
                p.setGenere(rs.getString(3));
                p.setAnnoPubblicazioni(rs.getString(4));
                p.setPrezzo(rs.getDouble(5));
                p.setSconto(rs.getInt(6));
                p.setTrama(rs.getString(7));
                p.setImmagine(rs.getString(8));
                p.setDisponibile(rs.getBoolean(9));
                p.setAutori(this.getScrittura(p.getIsbn()));
                libri.add(p);
            }
            return libri;
        } catch(SQLException e){
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ ensures \result == null || \result.getIsbn().equals(isbn);
    //@ ensures \result != null ==> \result.getTitolo() != null;
    //@ ensures \result != null ==> \result.getAutori() != null;
    //@ ensures \result != null ==> \result.getPrezzo() >= 0;
    //@ ensures \result != null ==> \result.getSconto() >= 0 && \result.getSconto() <= 100;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public Libro doRetrieveById(String isbn) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT * FROM Libro WHERE isbn=?");
            ps.setString(1, isbn);
            ResultSet rs = ps.executeQuery();
            if (rs.next()) {
                Libro p = new Libro();
                p.setIsbn(rs.getString(1));
                p.setTitolo(rs.getString(2));
                p.setGenere(rs.getString(3));
                p.setAnnoPubblicazioni(rs.getString(4));
                p.setPrezzo(rs.getDouble(5));
                p.setSconto(rs.getInt(6));
                p.setTrama(rs.getString(7));
                p.setImmagine(rs.getString(8));
                p.setDisponibile(rs.getBoolean(9));
                p.setAutori(this.getScrittura(p.getIsbn()));
                return p;
            }
            return null;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).getCf() != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public List<Autore> getScrittura(String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT cf FROM Scrittura WHERE isbn=?");
            ps.setString(1, isbn);
            ResultSet rs = ps.executeQuery();
            List<Autore> autori = new ArrayList<>();
            while (rs.next()) {
                String cf = rs.getString(1);
                AutoreDAO service = new AutoreDAO();
                autori.add(service.searchAutore(cf));
            }
            return autori;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).getIdReparto() > 0);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public List<Reparto> getAppartenenzaReparto(String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT idReparto FROM Appartenenza WHERE isbn=?");
            ps.setString(1, isbn);
            ResultSet rs = ps.executeQuery();
            List<Reparto> reparti = new ArrayList<>();
            while (rs.next()) {
                int idReparto = rs.getInt(1);
                RepartoDAO service = new RepartoDAO();
                reparti.add(service.doRetrieveById(idReparto));
            }
            return reparti;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i).getIdSede() > 0);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ pure
    public List<Sede> getPresenzaSede(String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT idSede FROM Presenza WHERE isbn=?");
            ps.setString(1, isbn);
            ResultSet rs = ps.executeQuery();
            List<Sede> sedi = new ArrayList<>();
            while (rs.next()) {
                int idSede = rs.getInt(1);
                SedeDAO service = new SedeDAO();
                sedi.add(service.doRetrieveById(idSede));
            }
            return sedi;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ requires autore != null;
    //@ requires autore.getCf() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    //@ signals (RuntimeException e) (* errore nella cancellazione dal database *);
    public void deleteAutoreScrittura(String isbn, Autore autore){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM Scrittura WHERE isbn=? AND cf=?");
            ps.setString(1, isbn);
            ps.setString(2, autore.getCf());

            AutoreDAO service = new AutoreDAO();
            service.deleteAutore(autore.getCf());
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires isbn != null;
    //@ requires autore != null;
    //@ requires autore.getCf() != null;
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public void addAutore(String isbn, Autore autore){
        try (Connection con = ConPool.getConnection()) {
            AutoreDAO autoreService=new AutoreDAO();
            if(autoreService.searchAutore(autore.getCf())==null)
                autoreService.doSave(autore);

            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO Scrittura (cf, isbn) VALUES(?,?)");
            ps.setString(1, autore.getCf());
            ps.setString(2, isbn);

            if (ps.executeUpdate() != 1) {
                throw new RuntimeException("INSERT error.");
            }
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    //@ requires query != null;
    //@ ensures \result != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
    //@ assignable \nothing;
    //@ signals_only RuntimeException;
    public List<Libro> Search(String query) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement("SELECT * FROM Libro WHERE titolo LIKE ? OR isbn LIKE ?");
            ps.setString(1, "%" + query + "%");
            ps.setString(2, query + "%");

            ResultSet rs = ps.executeQuery();
            List<Libro> libri = new ArrayList<>();
            while (rs.next()) {
                Libro p = new Libro();
                p.setIsbn(rs.getString(1));
                p.setTitolo(rs.getString(2));
                p.setGenere(rs.getString(3));
                p.setAnnoPubblicazioni(rs.getString(4));
                p.setPrezzo(rs.getDouble(5));
                p.setSconto(rs.getInt(6));
                p.setTrama(rs.getString(7));
                p.setImmagine(rs.getString(8));
                p.setDisponibile(rs.getBoolean(9));
                p.setAutori(this.getScrittura(p.getIsbn()));
                libri.add(p);
            }
            return libri;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }
}
