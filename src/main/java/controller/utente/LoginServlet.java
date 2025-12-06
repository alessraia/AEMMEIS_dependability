package controller.utente;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import model.wishList.WishList;
import model.wishList.WishListDAO;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

@WebServlet("/login-servlet")

public class LoginServlet extends HttpServlet {
    // Allow dependency injection for testing
    private UtenteDAO utenteDAO;
    private CarrelloDAO carrelloDAO;
    private WishListDAO wishListDAO;

    // Setters for dependency injection in tests
    public void setUtenteDAO(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }

    public void setCarrelloDAO(CarrelloDAO carrelloDAO) {
        this.carrelloDAO = carrelloDAO;
    }

    public void setWishListDAO(WishListDAO wishListDAO) {
        this.wishListDAO = wishListDAO;
    }
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        //controllo dei form
        String email = request.getParameter("email");
        String password = request.getParameter("pw");
        if((email==null || email.isEmpty() || !email.contains("@")) || (password== null || (password.isEmpty()) || password.length()>16)){
            ControlMethod.safeRedirect(response, "/WEB-INF/errorJsp/loginError.jsp", this);
            return;
        }
        else {
            Utente utente = new Utente();
            utente.setEmail(email);
            utente.setCodiceSicurezza(password);

            UtenteDAO service = (this.utenteDAO != null) ? this.utenteDAO : new UtenteDAO();

            if (service.doRetrieveByEmailPassword(utente.getEmail(), utente.getCodiceSicurezza()) == null) {
                RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/loginError.jsp");
                try {
                    dispatcher.forward(request, response);
                } catch (ServletException e) {
                    log("Errore durante il forward", e);
                } catch (IOException e) {
                    log("Errore di I/O durante il forward", e);
                }
            } else {
                HttpSession session = request.getSession();
                utente = service.doRetrieveById(email);
                session.setAttribute("utente", utente);

                Carrello carrelloLocale = (Carrello) session.getAttribute("carrello");// Recupera il carrello locale dalla sessione
                List<RigaCarrello> righeLocali = (carrelloLocale != null) ? carrelloLocale.getRigheCarrello() : null;

                CarrelloDAO carrelloService = (this.carrelloDAO != null) ? this.carrelloDAO : new CarrelloDAO();
                Carrello carrelloDb = null;

                if (carrelloService.doRetriveByUtente(utente.getEmail()) != null) {
                    carrelloDb = carrelloService.doRetriveByUtente(utente.getEmail());// Recupera il carrello dal database
                    List<RigaCarrello> rigaCarrelloDb = carrelloDb.getRigheCarrello();

                    if (righeLocali != null) {
                        // Fusiona i carrelli
                        for (int i = 0; i < righeLocali.size(); i++) {
                            RigaCarrello riga = righeLocali.get(i);
                            boolean flag = true;//non presente
                            for (int j = 0; j < rigaCarrelloDb.size() && flag; j++) {
                                RigaCarrello riga2 = rigaCarrelloDb.get(j);
                                if (riga2.getLibro().getIsbn().equals(riga.getLibro().getIsbn())) { //se l'isbn è già presente nel carrello del DB
                                    riga2.setQuantita(riga2.getQuantita() + riga.getQuantita());//incremento semplicemente la quantità
                                    flag = false;
                                }
                            }
                            if (flag) {
                                riga.setIdCarrello(carrelloDb.getIdCarrello());
                                rigaCarrelloDb.add(riga); //altrimenti lo aggiungo nel carrello
                            }
                        }
                    }
                }
                WishListDAO wishListService = (this.wishListDAO != null) ? this.wishListDAO : new WishListDAO();
                WishList wishList = wishListService.doRetrieveByEmail(utente.getEmail());

                session.setAttribute("carrello", carrelloDb);
                session.setAttribute("wishList", wishList);

                ControlMethod.safeRedirect(response, "index.html", this);
            }

        }


    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        try {
            this.doGet(req, resp);
        } catch (ServletException | IOException e) {
            log("Errore durante la gestione POST (doGet)", e);
        }
    }
}
