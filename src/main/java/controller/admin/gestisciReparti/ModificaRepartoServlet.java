package controller.admin.gestisciReparti;

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
        int idReparto = Integer.parseInt(request.getParameter("idReparto"));

        if (repartoDAO == null) {
            repartoDAO = new RepartoDAO();
        }
        
        // Check if reparto exists before trying to remove book
        if (repartoDAO.doRetrieveById(idReparto) != null) {
            repartoDAO.removeLibroReparto(idReparto, isbn);
        }

        response.sendRedirect("gestisci-reparti");
    }
}
