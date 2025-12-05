package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/gestisci-sedi")
public class GestisciSediServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        SedeDAO sedeService = new SedeDAO();
        List<Sede> sedi = sedeService.doRetrivedAll();
        request.setAttribute("sedi", sedi);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward ", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }


}