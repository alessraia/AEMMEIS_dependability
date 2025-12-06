package controller.admin.gestisciReparti;

import controller.utils.ControlMethod;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.io.IOException;

@WebServlet("/elimina-reparto")
public class EliminaRepartoServlet extends HttpServlet {
    private RepartoDAO repartoService;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoService = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        if (repartoService == null) {
            repartoService = new RepartoDAO();
        }

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
        repartoService.deleteReparto(idReparto);

        ControlMethod.safeRedirect(response, "gestisci-reparti", this);
       /* RequestDispatcher dispatcher = request.getRequestDispatcher("gestisci-reparti");
        dispatcher.forward(request, response);*/
    }

}
