package controller.utente.ordine;

import controller.utils.Validator;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.OrdineDAO;
import model.ordineService.RigaOrdine;
import model.utenteService.Utente;

import java.io.IOException;
import java.util.Iterator;
import java.util.List;

@WebServlet("/rimuovi-ordine")
public class RimuoviDaOrdine extends HttpServlet {
    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        HttpSession session = request.getSession();
        Utente utente = (Utente) session.getAttribute("utente");
        if (Validator.checkIfUserAdmin(utente)) {
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
            dispatcher.forward(request, response);
        }
        else {
            OrdineDAO ordineDAO = new OrdineDAO();

            // Ottiene i parametri dalla richiesta
            String isbn = request.getParameter("isbn");
            String idOrdine = (request.getParameter("idOrdine"));

            // Ottiene l'ordine dalla sessione
            List<RigaOrdine> righeOrdine = (List<RigaOrdine>) ordineDAO.doRetrieveById(idOrdine).getRigheOrdine();

            // Rimuove la riga d'ordine corrispondente
            if (isbn != null && !righeOrdine.isEmpty()) {
                Iterator<RigaOrdine> iterator = righeOrdine.iterator();
                while (iterator.hasNext()) {
                    RigaOrdine riga = iterator.next();
                    if (riga.getLibro().getIsbn().equals(isbn) && riga.getIdOrdine().equals(idOrdine)) {
                        iterator.remove();
                        break;
                    }
                }
            }

            // Reindirizza alla pagina di riepilogo dell'ordine
            response.sendRedirect("riepilogoOrdine.jsp");
        }
    }
}
