package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/gestisci-reparti")
public class GestisciRepartiServlet extends HttpServlet {
    private RepartoDAO repartoService;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoService = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        if (repartoService == null) {
            repartoService = new RepartoDAO();
        }
        List<Reparto> reparti = repartoService.doRetrivedAll();
        request.setAttribute("reparti", reparti);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp");
        dispatcher.forward(request, response);
    }


}
