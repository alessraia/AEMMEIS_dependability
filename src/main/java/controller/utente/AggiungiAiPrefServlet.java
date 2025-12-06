package controller.utente;

import controller.utils.ControlMethod;
import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import model.wishList.WishList;
import org.json.simple.JSONObject;

import java.io.IOException;
import java.util.ArrayList;

@WebServlet("/aggiungi-ai-preferiti")
public class AggiungiAiPrefServlet extends HttpServlet {
    private LibroDAO libroDAO = new LibroDAO();
    
    public void setLibroDAO(LibroDAO libroDAO) {
        this.libroDAO = libroDAO;
    }

    //Nuova servlet per aggiornare i preferiti (creata per utilizzare AJAX)
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String isbn = request.getParameter("isbn"); // Ottieni l'ISBN dal parametro della richiesta
        Libro libro = libroDAO.doRetrieveById(isbn);
        HttpSession session = request.getSession();
        Utente utente= (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            }
        } else if(utente==null){
            ControlMethod.safeSendError(response, HttpServletResponse.SC_UNAUTHORIZED, "User not logged in", this);
        }
        else {
            JSONObject jsonResponse = new JSONObject();
            //boolean
            jsonResponse.put("isInWishList", true); // Indica se il libro è ora nei preferiti

            // Aggiungi l'ISBN alla WishList (o al database)
            WishList wishList = (WishList) session.getAttribute("wishList");
            boolean flag = true; // libro non presente
            if (wishList != null && wishList.getLibri() != null) {
                for (int i = 0; i < wishList.getLibri().size() && flag; i++) {
                    if (wishList.getLibri().get(i).equals(libro)) {
                        wishList.getLibri().remove(i); // libro già presente, lo rimuovo
                        flag = false;
                        jsonResponse.put("isInWishList", false); // Indica che il libro non è più nei preferiti
                    }
                }
                if (flag)// se il libro non è presente, lo aggiungo
                    wishList.getLibri().add(libro);

            } else {
                wishList.setLibri(new ArrayList<model.libroService.Libro>());
                wishList.getLibri().add(libro);

            }

            session.setAttribute("wishList", wishList);

            // Invia una risposta al client (ad esempio, un oggetto JSON)
            response.setContentType("application/json");
            response.getWriter().write(jsonResponse.toString());
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

