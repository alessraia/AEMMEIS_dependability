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
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.utenteService.Utente;
import org.json.simple.JSONObject;

import java.io.IOException;
import java.util.List;

@WebServlet("/rimuovi-dal-carrello")
public class RimuoviDalCartServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String isbn = request.getParameter("isbn");

        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if(Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward verso /WEB-INF/results/admin/homepageAdmin.jsp", e);
            }
            return;
        }
        Carrello carrello = (Carrello) session.getAttribute("carrello");

        LibroDAO libroService = new LibroDAO();
        Libro libro = libroService.doRetrieveById(isbn);

        List<RigaCarrello> righeCarrello = carrello.getRigheCarrello();
        boolean success=false;
        if(carrello!=null) {
            for (int i = 0; i < righeCarrello.size(); i++) {
                RigaCarrello riga = righeCarrello.get(i);
                if (riga.getLibro().equals(libro)) {
                    righeCarrello.remove(i);//quando trova il libro lo rimuove
                    success=true;
                }
            }
            // Crea una risposta JSON per indicare lo stato della rimozione
            JSONObject jsonResponse = new JSONObject();
            jsonResponse.put("success", success);

            // Imposta il tipo di contenuto della risposta
            response.setContentType("application/json");

            // Invia la risposta JSON al client
            try {
                response.getWriter().write(jsonResponse.toString());
            } catch (IOException e) {
                log("Errore durante la scrittura della risposta JSON", e);
            }
        } else {
            // Se il carrello non esiste, restituisci un errore
            ControlMethod.safeSendError(response, HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "Il carrello non è stato trovato", this);
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
