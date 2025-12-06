package controller.admin.gestisciSedi;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import model.libroService.SedeDAO;

import java.io.IOException;

@WebServlet("/elimina-sede")
public class EliminaSedeServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        SedeDAO sedeService = new SedeDAO();

        String idParam = request.getParameter("idSede");
        int idSede;

        try {
            idSede = Integer.parseInt(idParam);
        } catch (NumberFormatException ex) {
            log("Parametro 'id' non valido: " + idParam, ex);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/erroreForm.jsp", e);
            }
            return;
        }

        sedeService.deleteSede(idSede);

        ControlMethod.safeRedirect(response, "gestisci-sedi", this);
    }
}