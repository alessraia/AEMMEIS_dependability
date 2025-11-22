package model.wishList;

import model.ConPool;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class WishListDAO {

    private final LibroDAO libroDAO;

    public WishListDAO() {
        this(new LibroDAO());
    }

    public WishListDAO(LibroDAO libroDAO) {
        this.libroDAO = libroDAO;
    }

    /*@ public behavior
      @   requires wishList != null
      @        && wishList.getEmail() != null
      @        && wishList.getEmail().length() > 0
      @        && isbn != null
      @        && isbn.length() == 13;
      @   signals (RuntimeException e) true;
      @   signals_only RuntimeException;
      @*/
    public void doSave(WishList wishList, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps = con.prepareStatement(
                    "INSERT INTO WishList (email, isbn) VALUES(?,?)");
            ps.setString(1, wishList.getEmail());
            ps.setString(2, isbn);

               if (ps.executeUpdate() != 1) {
                   throw new RuntimeException("INSERT error.");
               }

           } catch (SQLException e) {
               throw new RuntimeException(e);
           }


    }

    /*@ public behavior
      @   requires email != null && email.length() > 0;
      @   ensures \result != null;
      @   signals (RuntimeException e) true;
      @   signals_only RuntimeException;
      @*/
    public WishList doRetrieveByEmail(String email) {
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("SELECT email, isbn FROM WishList WHERE email=?");
            ps.setString(1, email);
            ResultSet rs = ps.executeQuery();
            WishList wishlist = new WishList();
            wishlist.setLibri(new ArrayList<Libro>());
            while (rs.next()) {
                wishlist.setEmail(rs.getString(1));
                Libro libro = libroDAO.doRetrieveById(rs.getString(2));
                wishlist.addLibro(libro);
            }
            return wishlist;
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0
      @        && isbn != null && isbn.length() == 13;
      @   signals (RuntimeException e) true;
      @   signals_only RuntimeException;
      @*/
    public void deleteLibro(String email, String isbn){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM WishList WHERE email=? AND isbn =?");
            ps.setString(1, email);
            ps.setString(2, isbn);
            if(ps.executeUpdate() != 1)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }

    /*@ public behavior
      @   requires email != null && email.length() > 0;
      @   signals (RuntimeException e) true;
      @   signals_only RuntimeException;
      @*/
    public void deleteWishListByEmail(String email){
        try (Connection con = ConPool.getConnection()) {
            PreparedStatement ps =
                    con.prepareStatement("DELETE FROM WishList WHERE email=?");
            ps.setString(1, email);
            if(ps.executeUpdate() <= 0)
                throw new RuntimeException("DELETE error.");
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
    }
}
