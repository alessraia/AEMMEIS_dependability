package controller.admin.gestisciReparti;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;

import java.io.IOException;

@WebServlet("/modifica-reparto")
public class ModificaRepartoServlet extends HttpServlet {
    private RepartoDAO repartoDAO;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoDAO = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {

        String isbn = request.getParameter("isbn");

        String idParam = request.getParameter("idReparto");
        int idReparto;

        try {
            idReparto = Integer.parseInt(idParam);
        } catch (NumberFormatException ex) {
            log("Parametro 'id' non valido: " + idParam, ex);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);
            }
            return;
        }

        if (repartoDAO == null) {
            repartoDAO = new RepartoDAO();
        }
        
        // Check if reparto exists before trying to remove book
        if (repartoDAO.doRetrieveById(idReparto) != null) {
            repartoDAO.removeLibroReparto(idReparto, isbn);
        }

        ControlMethod.safeRedirect(response, "gestisci-reparti", this);
    }
}
